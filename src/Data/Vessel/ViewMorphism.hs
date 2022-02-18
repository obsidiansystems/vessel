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
import Data.Proxy
import Data.Void
import Control.Arrow (Kleisli(..))
import qualified Control.Category.Monoidal as Cat
import qualified Control.Category.Associative as Cat
import qualified Control.Category.Braided as Cat
import qualified Control.Categorical.Bifunctor as Cat
import Data.Vessel.Orphans ()


type family ViewQueryResult (v :: k) :: k

type instance ViewQueryResult (Const g x) = Identity x
type instance ViewQueryResult (Const g) = Identity
type instance ViewQueryResult (Proxy x) = Identity x
type instance ViewQueryResult Proxy = Identity
type instance ViewQueryResult (These a b) = These (ViewQueryResult a) (ViewQueryResult b)
type instance ViewQueryResult Void = Void



-- | a way to bundle a request of partially loaded information
--
-- `m` counts the number of occurrences in the query of `q` in `p`
-- `n` counts the number of occurrences in the result of `p` in `q`
--
-- a ViewHalfMorphism representing the pull side, something like
-- $ViewHalfMorphism Identity Maybe leaf root$ expresses a way to turn a leaf
-- query into a root query, and to look up a leaf query result in a root query
-- result, if its present.
--
-- respectively , a push side ViewHalfMorphism, something like
-- $ViewHalfMorphism Maybe Identity root leaf$ is a way to look up a leaf query
-- in a root query, if its there, and a way to turn a leaf result into a root
-- result.
data ViewHalfMorphism m n p q = ViewHalfMorphism
  { _viewMorphism_mapQuery :: p -> m q
  , _viewMorphism_mapQueryResult :: ViewQueryResult q -> n (ViewQueryResult p) -- TODO Loading data
  }

mapViewHalfMorphism
  :: Monad m
  => ViewHalfMorphism f g a b
  -> (f b -> m (ViewQueryResult b))
  -> a
  -> m (g (ViewQueryResult a))
mapViewHalfMorphism v f x =
  _viewMorphism_mapQueryResult v <$> f (_viewMorphism_mapQuery v x)

traverseViewHalfMorphism
  :: (Traversable f, Applicative m)
  => ViewHalfMorphism f g a b
  -> (b -> m (ViewQueryResult b))
  -> a
  -> m (f (g (ViewQueryResult a)))
traverseViewHalfMorphism v f x =
  traverse (fmap (_viewMorphism_mapQueryResult v) . f) (_viewMorphism_mapQuery v x)

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
  => ViewMorphism m n a c -> ViewMorphism m n b c -> ViewMorphism m n (These a b) c
zipViewMorphism (ViewMorphism f f') (ViewMorphism g g') = ViewMorphism (toZipViewMorphism f g) (fromZipViewMorphism f' g')

toZipViewMorphism :: forall m n a b c. (Semialign n, Semigroup (m c)) => ViewHalfMorphism m n a c -> ViewHalfMorphism m n b c -> ViewHalfMorphism m n (These a b) c
toZipViewMorphism (ViewHalfMorphism a2c c2a' ) (ViewHalfMorphism b2c c2b' ) = ViewHalfMorphism
    { _viewMorphism_mapQuery = these a2c b2c $ \x y -> a2c x <> b2c y
    , _viewMorphism_mapQueryResult = \r -> align (c2a' r) (c2b' r)
    }
fromZipViewMorphism
  :: forall m n a b c.
  ( Applicative m
  , Semigroup (n (ViewQueryResult c))
  ) => ViewHalfMorphism m n c a -> ViewHalfMorphism m n c b -> ViewHalfMorphism m n c (These a b)
fromZipViewMorphism (ViewHalfMorphism c2a a2c') (ViewHalfMorphism c2b b2c') = ViewHalfMorphism
    { _viewMorphism_mapQuery = \r -> liftA2 These (c2a r) (c2b r)
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


type instance ViewQueryResult (These a b) = These (ViewQueryResult a) (ViewQueryResult b)

type instance ViewQueryResult Void = Void

instance (Monad f, Monad g) => Cat.PFunctor These (ViewHalfMorphism f g) (ViewHalfMorphism f g) where
  first (ViewHalfMorphism f g) = ViewHalfMorphism
    (runKleisli $ Cat.first $ Kleisli f)
    (runKleisli $ Cat.first $ Kleisli g)

instance (Monad f, Monad g) => Cat.QFunctor These (ViewHalfMorphism f g) (ViewHalfMorphism f g) where
  second (ViewHalfMorphism f g) = ViewHalfMorphism
    (runKleisli $ Cat.second $ Kleisli f)
    (runKleisli $ Cat.second $ Kleisli g)

instance (Monad f, Monad g) => Cat.Bifunctor These (ViewHalfMorphism f g) (ViewHalfMorphism f g) (ViewHalfMorphism f g) where
  bimap (ViewHalfMorphism f g) (ViewHalfMorphism f' g') = ViewHalfMorphism
    (runKleisli $ Cat.bimap (Kleisli f) (Kleisli f'))
    (runKleisli $ Cat.bimap (Kleisli g) (Kleisli g'))
instance (Monad f, Monad g) => Cat.Associative (ViewHalfMorphism f g) These where
  associate = ViewHalfMorphism (runKleisli Cat.associate) (runKleisli Cat.disassociate)
  disassociate = ViewHalfMorphism (runKleisli Cat.disassociate) (runKleisli Cat.associate)

instance (Monad f, Monad g) => Cat.Braided (ViewHalfMorphism f g) These where
  braid = ViewHalfMorphism (runKleisli Cat.braid) (runKleisli Cat.braid)

instance (Monad f, Monad g) => Cat.Symmetric (ViewHalfMorphism f g) These where

instance (Monad f, Monad g) => Cat.Monoidal (ViewHalfMorphism f g) These where
  type Id (ViewHalfMorphism f g) These = Cat.Id (Kleisli Identity) These
  idl = ViewHalfMorphism (runKleisli Cat.idl) (runKleisli Cat.coidl)
  idr = ViewHalfMorphism (runKleisli Cat.idr) (runKleisli Cat.coidr)
  coidl = ViewHalfMorphism (runKleisli Cat.coidl) (runKleisli Cat.idl)
  coidr = ViewHalfMorphism (runKleisli Cat.coidr) (runKleisli Cat.idr)


