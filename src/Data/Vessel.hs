{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE InstanceSigs #-}

module Data.Vessel where

import Data.Aeson
import Data.Align
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Constraint
import Data.Constraint.Extras
import Data.Constraint.Forall
import qualified Data.Dependent.Map.Monoidal as DMap
import Data.Dependent.Map.Monoidal (MonoidalDMap)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Dependent.Sum
import Data.Dependent.Sum.Orphans ()
import Data.Functor.Compose
import Data.Functor.Const
import Data.GADT.Compare
import Data.Maybe
import Data.Semigroup
import Data.Some hiding (This)
import Data.These
import Prelude hiding (lookup, map)
import Reflex (Group(..), Additive, Query(..), FunctorMaybe(..), ffilter)

import Data.TSum

--import qualified Data.Map.Monoidal as Map
--import Data.Map.Monoidal (MonoidalMap)

{-
data TV a where
  TV_Email :: TV (Mapf (Id Email') (First (Maybe EmailView)))
-}

--newtype Mapf k v f = Mapf (MonoidalMap k (f v))

newtype FlipAp (a :: * -> *) (f :: (* -> *) -> *) = FlipAp { unFlipAp :: f a }

newtype Vessel (f :: ((* -> *) -> *) -> *) (g :: * -> *) = Vessel { unVessel :: MonoidalDMap f (FlipAp g) }

singletonVessel :: k v -> v g -> Vessel k g
singletonVessel k v = Vessel (DMap.singleton k (FlipAp v))

--class c (t g) => ApClass (c :: k' -> Constraint) (g :: k) (t :: k -> k') where

instance (ForallF Semigroup f, Semigroup (g x)) => Semigroup (Compose f g x) where

instance (ForallF Monoid f, Semigroup (g x)) => Monoid (Compose f g x) where

instance Semigroup (Vessel f g) where
  (<>) = undefined

-- disperseQ f m = Map.unionsWith (<>) . map (\(k :=> v) -> fmap (DMap.singleton k) (f v)) . DMap.toList

class View v where
  disperseV :: (ForallF Monoid t, Functor t) => (forall x. f x -> t (g x)) -> v f -> t (v g)
  condenseV :: (ForallF Monoid g, Ord t) => (forall x. Map t (g x) -> f x) -> Map t (v g) -> v f
  hoistV :: (forall a. f a -> g a) -> v f -> v g
  traverseV :: (Applicative m) => (forall a. f a -> m (g a)) -> v f -> m (v g)

has :: forall c f a r. (Has c f) => f a -> (c a => r) -> r
has k r | (Dict :: Dict (c a)) <- argDict k = r

whichever :: forall c t a r. (ForallF c t) => (c (t a) => r) -> r
whichever r = r \\ (instF :: ForallF c t :- c (t a))

instance (Has View k, GCompare k) => View (Vessel k) where
  disperseV :: forall t f g. (ForallF Monoid t, Functor t) => (forall x. f x -> t (g x)) -> Vessel k f -> t (Vessel k g)
  disperseV f (Vessel m) = whichever @Monoid @t @(Vessel k g) $ mconcat
    . fmap (\(k :=> FlipAp v) -> has @View k $ fmap (singletonVessel k) $ disperseV f v)
    . DMap.toList $ m
  hoistV :: (forall a. f a -> g a) -> Vessel k f -> Vessel k g
  hoistV f (Vessel m) = Vessel (DMap.mapWithKey (\k (FlipAp v) -> has @View k $ FlipAp (hoistV f v)) m)
  traverseV :: (Applicative m) => (forall a. f a -> m (g a)) -> Vessel k f -> m (Vessel k g)
  traverseV f (Vessel m) = fmap Vessel (DMap.traverseWithKey (\k (FlipAp v) -> has @View k $ fmap FlipAp (traverseV f v)) m)
  condenseV :: forall g t f. (ForallF Monoid g, Ord t) => (forall x. Map t (g x) -> f x) -> Map t (Vessel k g) -> Vessel k f
  condenseV f m = Vessel . DMap.mapWithKey (\k (Compose m) -> FlipAp . has @View k (condenseV f) $ fmap unFlipAp m)
                . mconcat
                . fmap (\(k, (Vessel v)) -> DMap.map (Compose . Map.singleton k) v) $ Map.toList m

-- TODO: Class for fromDistinctAscList? In disperseV and condenseV, we might be able to improve the cost relative to
-- combining many singleton maps, if we know those maps are presented to us in sorted order.
{-
foldMapQ :: (Monoid m) => (forall a. f a -> m) -> v f -> m
fmapMaybeQ :: (forall a. f a -> Maybe (g a)) -> v f -> v g
alignWithQ :: (forall a. These (f a) (g a) -> h a) -> (v f, v g) -> v h
unalignWithQ :: (forall a. f a -> These (g a) (h a)) -> v f -> (v g, v h)
-}