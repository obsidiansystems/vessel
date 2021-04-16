{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE UndecidableInstances #-}

module Data.Vessel.ViewMorphism where
------- Selectable convenience class -------

import Prelude hiding (id, (.))
import Control.Monad
import Control.Applicative
import Control.Category
import Data.Bifunctor
import Data.Functor.Identity
import Data.These
import Reflex.Query.Class
import Reflex.Class
import Data.Align
import Data.Vessel.Internal ()

type family ViewQueryResult (v :: k) :: k

type instance ViewQueryResult (Const g x) = Identity x
type instance ViewQueryResult (Const g) = Identity
type instance ViewQueryResult (a, b) = These (ViewQueryResult a) (ViewQueryResult b)

-- a way to request partially loaded information;
data ViewHalfMorphism m n p q = ViewHalfMorphism
  { _viewMorphism_mapQuery :: p -> m q
  , _viewMorphism_mapQueryResult :: ViewQueryResult q -> n (ViewQueryResult p) -- TODO Loading data
  }

data ViewMorphism m n p q = ViewMorphism
  { _viewMorphism_to ::   ViewHalfMorphism m n p q
  , _viewMorphism_from :: ViewHalfMorphism n m q p
  }

type ViewMorphismSimple = ViewMorphism Identity Maybe

instance (Monad m, Monad n) => Category (ViewHalfMorphism n m) where
  id = ViewHalfMorphism pure pure
  ViewHalfMorphism f f' . ViewHalfMorphism g g' = ViewHalfMorphism (f <=< g) (f' >=> g')

instance (Monad m, Monad n) => Category (ViewMorphism m n) where
  id = ViewMorphism id id
  ViewMorphism f f' . ViewMorphism g g' = ViewMorphism (f . g) (g' . f')

instance (Semigroup (m b) , Semigroup (n (ViewQueryResult a))) => Semigroup (ViewHalfMorphism m n a b) where
  ViewHalfMorphism f f' <> ViewHalfMorphism g g' = ViewHalfMorphism (f <> g) (f' <> g')

instance (Monoid (m b) , Monoid (n (ViewQueryResult a))) => Monoid (ViewHalfMorphism m n a b) where
  mappend = (<>)
  mempty = ViewHalfMorphism mempty mempty

instance
    ( Semigroup (m b), Semigroup (m (ViewQueryResult b))
    , Semigroup (n a), Semigroup (n (ViewQueryResult a))
    ) => Semigroup (ViewMorphism m n a b) where
  ViewMorphism f f' <> ViewMorphism g g' = ViewMorphism (f <> g) (f' <> g')

instance
    ( Monoid (m b), Monoid (m (ViewQueryResult b))
    , Monoid (n a), Monoid (n (ViewQueryResult a))
    )  => Monoid (ViewMorphism m n a b) where
  mappend = (<>)
  mempty = ViewMorphism mempty mempty

-- | query for two things simultaneously, return as much result as is available.
zipViewMorphism
  ::
  ( Semigroup (m c)
  , Semigroup (m (ViewQueryResult c))
  , Semialign n
  , Applicative n
  )
  => ViewMorphism m n a c -> ViewMorphism m n b c -> ViewMorphism m n (a, b) c
zipViewMorphism (ViewMorphism f f') (ViewMorphism g g') = ViewMorphism (toZipViewMorphism f g) (fromZipViewMorphism f' g')

toZipViewMorphism :: forall m n a b c. (Semialign n, Semigroup (m c)) => ViewHalfMorphism m n a c -> ViewHalfMorphism m n b c -> ViewHalfMorphism m n (a, b) c
toZipViewMorphism (ViewHalfMorphism a2c c2a' ) (ViewHalfMorphism b2c c2b' ) = ViewHalfMorphism
    { _viewMorphism_mapQuery = \(x, y) -> a2c x <> b2c y
    , _viewMorphism_mapQueryResult = \r -> align (c2a' r) (c2b' r)
    }
fromZipViewMorphism
  :: forall m n a b c.
  ( Applicative m
  , Semigroup (n (ViewQueryResult c))
  ) => ViewHalfMorphism m n c a -> ViewHalfMorphism m n c b -> ViewHalfMorphism m n c (a, b)
fromZipViewMorphism (ViewHalfMorphism c2a a2c') (ViewHalfMorphism c2b b2c') = ViewHalfMorphism
    { _viewMorphism_mapQuery = \r -> liftA2 (,) (c2a r) (c2b r)
    , _viewMorphism_mapQueryResult = these id id ((<>)) . bimap a2c' b2c'
    }

queryViewMorphism :: forall t (p :: *) (q :: *) m partial.
  ( Reflex t
  , MonadQuery t q m
  , Monad m
  , QueryResult q ~ ViewQueryResult q
  )
  => p -> Dynamic t (ViewMorphism Identity partial p q) -> m (Dynamic t (partial (ViewQueryResult p)))
queryViewMorphism x q = do
  v :: Dynamic t (QueryResult q) <- queryDyn $ (\(ViewMorphism (ViewHalfMorphism f _) _) -> runIdentity $ f x) <$> q
  return $ (\v' (ViewMorphism  (ViewHalfMorphism _ g) _) -> g v') <$> v <*> q

