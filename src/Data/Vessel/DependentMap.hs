{-# LANGUAGE AllowAmbiguousTypes #-}
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

module Data.Vessel.DependentMap where

import Data.Aeson
import Data.Bifunctor
import Data.Constraint.Extras
import Data.Constraint.Forall
import Data.Dependent.Map.Monoidal (MonoidalDMap(..))
import Data.Functor.Compose
import Data.GADT.Compare
import Data.Some (Some(Some))
import GHC.Generics
import Data.Functor.Identity
import Data.Dependent.Sum
import Data.Dependent.Sum.Orphans ()
import Data.Set (Set)
import qualified Data.Set as Set
import Reflex.Patch (Group(..), Additive)
import qualified Data.Dependent.Map as DMap'
import qualified Data.Dependent.Map.Monoidal as DMap

import Data.Vessel.Class
import Data.Vessel.Selectable
import Data.Vessel.Internal

-- | A functor-indexed container corrresponding to DMap k v.
newtype DMapV (k :: * -> *) (v :: * -> *) g = DMapV { unDMapV :: MonoidalDMap k (Compose g v) }
  deriving (Generic)

deriving instance (GCompare k, Has' Eq k (Compose g v)) => Eq (DMapV k v g)
deriving instance (GCompare k, Has' Eq k (Compose g v), Has' Ord k (Compose g v)) => Ord (DMapV k v g)
deriving instance (GCompare k, Has' Semigroup k (Compose g v)) => Semigroup (DMapV k v g)
deriving instance (GCompare k, Has' Semigroup k (Compose g v), Has' Monoid k (Compose g v)) => Monoid (DMapV k v g)
deriving instance (GCompare k, Has' Semigroup k (Compose g v), Has' Monoid k (Compose g v), Has' Group k (Compose g v)) => Group (DMapV k v g)
deriving instance (GCompare k, Has' Semigroup k (Compose g v), Has' Monoid k (Compose g v), Has' Group k (Compose g v), Has' Additive k (Compose g v)) => Additive (DMapV k v g)

instance (Has' ToJSON k (Compose g v), ForallF ToJSON k) => ToJSON (DMapV k v g)

instance (Has' FromJSON k (Compose g v), FromJSON (Some k), GCompare k) => FromJSON (DMapV k v g)

deriving instance (ForallF Show k, Has' Show k (Compose g v)) => Show (DMapV k v g)

instance (GCompare k) => View (DMapV k v) where
  cropV f (DMapV s) (DMapV i) = collapseNullV $ DMapV (DMap.intersectionWithKey (\_ (Compose x) (Compose y) -> Compose $ f x y) s i)
  nullV (DMapV m) = DMap.null m
  condenseV m = DMapV . DMap.map assocLCompose . condenseV . fmap unDMapV $ m
  disperseV (DMapV m) = fmap DMapV . disperseV . DMap.map assocRCompose $ m
  mapV f (DMapV m) = DMapV $ DMap.map (\(Compose x) -> Compose (f x)) m
  traverseV f (DMapV m) = DMapV <$> DMap.traverseWithKey (\_ (Compose x) -> Compose <$> f x) m
  mapMaybeV f (DMapV (MonoidalDMap m)) = collapseNullV $ DMapV $ MonoidalDMap $
    DMap'.mapMaybe (fmap Compose . f . getCompose) m
  alignWithV f (DMapV a) (DMapV b) = DMapV (alignWithKeyMonoidalDMap (\_ x -> Compose . f $ bimap getCompose getCompose x) a b)
  alignWithMaybeV f (DMapV a) (DMapV b) = collapseNullV . DMapV $
     alignWithKeyMaybeMonoidalDMap (\_ x -> fmap Compose $ f (bimap getCompose getCompose x)) a b

instance (GCompare k) => EmptyView (DMapV k v) where
  emptyV = DMapV DMap.empty

instance (GCompare k) => Selectable (DMapV k v) (Set (Some k)) where
  type Selection (DMapV k v) (Set (Some k)) = MonoidalDMap k v
  selector p s = DMapV . DMap.fromListWithKey (\_ x _ -> x) $
    fmap (\(Some k) -> k :=> Compose p) (Set.toList s)
  selection _ (DMapV m) = DMap.map (\(Compose (Identity v)) -> v) m

