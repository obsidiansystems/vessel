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
import qualified Data.Dependent.Map as DMap'
import Data.Dependent.Map.Monoidal (MonoidalDMap(..))
import qualified Data.Dependent.Map.Monoidal as MonoidalDMap
import qualified Data.Dependent.Map.Monoidal as DMap
import Data.Dependent.Sum
import Data.Dependent.Sum.Orphans ()
import Data.Functor.Compose
import Data.Functor.Identity
import Data.GADT.Compare
import Data.Patch (Group(..))
import Data.Semigroup.Commutative
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Some (Some(Some))
import GHC.Generics

import Data.Vessel.Class
import Data.Vessel.Internal
import Data.Vessel.Selectable

-- | A functor-indexed container corrresponding to DMap k v.
newtype DMapV (k :: x -> *) (v :: x -> *) g = DMapV { unDMapV :: MonoidalDMap k (g :.: v) }
  deriving (Generic)

deriving instance (GCompare k, Has' Eq k (g :.: v)) => Eq (DMapV k v g)
deriving instance (GCompare k, Has' Eq k (g :.: v), Has' Ord k (g :.: v)) => Ord (DMapV k v g)
deriving instance (GCompare k, Has' Semigroup k (g :.: v)) => Semigroup (DMapV k v g)
deriving instance (GCompare k, Has' Semigroup k (g :.: v), Has' Monoid k (g :.: v)) => Monoid (DMapV k v g)
deriving instance (GCompare k, Has' Semigroup k (g :.: v), Has' Monoid k (g :.: v), Has' Group k (g :.: v)) => Group (DMapV k v g)
deriving instance (GCompare k, Has' Semigroup k (g :.: v), Has' Monoid k (g :.: v), Has' Group k (g :.: v), Has' Commutative k (g :.: v)) => Commutative (DMapV k v g)

instance (Has' ToJSON k (g :.: v), ForallF ToJSON k) => ToJSON (DMapV k v g)

instance (Has' FromJSON k (g :.: v), FromJSON (Some k), GCompare k) => FromJSON (DMapV k v g)

deriving instance (ForallF Show k, Has' Show k (g :.: v)) => Show (DMapV k v g)

instance (GCompare k) => View (DMapV k v) where
  cropV f (DMapV s) (DMapV i) = collapseNullV $ DMapV (DMap.intersectionWithKey (\_ (Comp1 x) (Comp1 y) -> Comp1 $ f x y) s i)
  nullV (DMapV m) = DMap.null m
  condenseV m = DMapV . DMap.map assocLComposeComp . condenseV . fmap unDMapV $ m
  disperseV (DMapV m) = fmap DMapV . disperseV . DMap.map assocRComposeComp $ m
  mapV f (DMapV m) = DMapV $ DMap.map (\(Comp1 x) -> Comp1 (f x)) m
  traverseV f (DMapV m) = DMapV <$> DMap.traverseWithKey (\_ (Comp1 x) -> Comp1 <$> f x) m
  mapMaybeV f (DMapV (MonoidalDMap m)) = collapseNullV $ DMapV $ MonoidalDMap $
    DMap'.mapMaybe (fmap Comp1 . f . unComp1) m
  alignWithV f (DMapV a) (DMapV b) = DMapV (alignWithKeyMonoidalDMap (\_ x -> Comp1 . f $ bimap unComp1 unComp1 x) a b)
  alignWithMaybeV f (DMapV a) (DMapV b) = collapseNullV . DMapV $
     alignWithKeyMaybeMonoidalDMap (\_ x -> fmap Comp1 $ f (bimap unComp1 unComp1 x)) a b

instance (GCompare k) => EmptyView (DMapV k v) where
  emptyV = DMapV DMap.empty

instance (GCompare k) => Selectable (DMapV k v) (Set (Some k)) where
  type Selection (DMapV k v) (Set (Some k)) = MonoidalDMap k v
  selector p s = DMapV . DMap.fromListWithKey (\_ x _ -> x) $
    fmap (\(Some k) -> k :=> Comp1 p) (Set.toList s)
  selection _ (DMapV m) = DMap.map (\(Comp1 (Identity v)) -> v) m

singletonDMapV :: k a -> g (v a) -> DMapV k v g
singletonDMapV k v = DMapV $ MonoidalDMap.singleton k (Comp1 v)

lookupDMapV :: GCompare k => k a -> DMapV k v g -> Maybe (g (v a))
lookupDMapV k (DMapV m) = unComp1 <$> MonoidalDMap.lookup k m
