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

type family ViewQueryResult (v :: k) :: k

type instance ViewQueryResult (Const g x) = Identity x
type instance ViewQueryResult (Const g) = Identity
type instance ViewQueryResult (a, b) = These (ViewQueryResult a) (ViewQueryResult b)

-- a way to request partially loaded information;
data ViewMorphism p q = ViewMorphism
  { _viewMorphism_mapQuery :: p -> q
  , _viewMorphism_mapQueryResult :: ViewQueryResult q -> Maybe (ViewQueryResult p) -- TODO Loading data
  , _viewMorphism_buildResult :: ViewQueryResult p -> ViewQueryResult q
  }

instance Category ViewMorphism where
  id = ViewMorphism id Just id
  ViewMorphism f f' f'' . ViewMorphism g g' g'' = ViewMorphism (f . g) (f' >=> g') (f'' . g'')

instance (Semigroup b, Semigroup (ViewQueryResult b)) => Semigroup (ViewMorphism a b) where
  ViewMorphism f f' f'' <> ViewMorphism g g' g'' = ViewMorphism (f <> g) (\x -> f' x <|> g' x) (f'' <> g'')

instance (Monoid b, Monoid (ViewQueryResult b))  => Monoid (ViewMorphism a b) where
  mappend = (<>)
  mempty = ViewMorphism (const mempty) (const Nothing) (const mempty)

-- | query for two things simultaneously, return as much result as is available.
zipViewMorphism :: (Semigroup c, Semigroup (ViewQueryResult c))  => ViewMorphism a c -> ViewMorphism b c -> ViewMorphism (a, b) c
zipViewMorphism (ViewMorphism f f' f'') (ViewMorphism g g' g'') = ViewMorphism
  { _viewMorphism_mapQuery = \(x, y) -> f x <> g y
  , _viewMorphism_mapQueryResult = \r -> align (f' r) (g' r)
  , _viewMorphism_buildResult = these id id (<>) . bimap f'' g''
  }

queryViewMorphism :: forall t (p :: *) (q :: *) m.
  ( Reflex t
  , MonadQuery t q m
  , Monad m
  , QueryResult q ~ ViewQueryResult q
  )
  => p -> Dynamic t (ViewMorphism p q) -> m (Dynamic t (Maybe (ViewQueryResult p)))
queryViewMorphism x q = do
  v :: Dynamic t (QueryResult q) <- queryDyn $ (\(ViewMorphism f _ _) -> f x) <$> q
  return $ (\v' (ViewMorphism _ g _) -> g v') <$> v <*> q

