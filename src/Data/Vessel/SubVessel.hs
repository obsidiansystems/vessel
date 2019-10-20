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

module Data.Vessel.SubVessel where


import Data.Aeson
import Data.Constraint
import Data.Constraint.Extras
import Data.Foldable
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.GADT.Compare
import Data.Map (Map)
import Data.Proxy
import Data.Set (Set)
import Data.Some (Some(Some))
import GHC.Generics
import Reflex.Patch (Group(..), Additive)
import Reflex.Query.Class
import qualified Data.Map as Map'

import Data.Vessel.Class
import Data.Vessel.Vessel
import Data.Vessel.Internal
import Data.Vessel.ViewMorphism

data SubVesselKey k (f :: (* -> *) -> *) (g :: (* -> *) -> *) where
  SubVesselKey :: k -> SubVesselKey k f f

instance FromJSON k => FromJSON (Some (SubVesselKey k v)) where parseJSON v = Some . SubVesselKey <$> parseJSON v
instance ToJSON k => ToJSON (SubVesselKey k f g) where toJSON (SubVesselKey k) = toJSON k

instance ArgDict c (SubVesselKey k f) where
  type ConstraintsFor (SubVesselKey k f) c = c f
  argDict (SubVesselKey _) = Dict

instance Eq k => GEq (SubVesselKey k v) where
  geq (SubVesselKey x) (SubVesselKey y) = case x == y of
    True -> Just Refl
    False -> Nothing

instance Ord k => GCompare (SubVesselKey k v) where
  gcompare (SubVesselKey x) (SubVesselKey y) = case compare x y of
    LT -> GLT
    EQ -> GEQ
    GT -> GGT

newtype SubVessel (k :: *)  (v :: (* -> *) -> *) (f :: * -> *) = SubVessel { unSubVessel :: Vessel (SubVesselKey k v) f }
  deriving (FromJSON, ToJSON, Semigroup, Monoid, Generic, Group, Additive, Eq)

-- slightly nicer unwrapper compared to unSubVessel
getSubVessel :: Ord k => SubVessel k v f -> Map k (v f)
getSubVessel = Map'.fromListWith (error "getSubVessel:collision") . fmap (\(SubVesselKey k :~> v) -> (k, v)) . toListV . unSubVessel

instance (Ord k, View v) => View (SubVessel k v)

instance (Ord k, Semigroup (v Identity), View v) => Query (SubVessel k v (Const x)) where
  type QueryResult (SubVessel k v (Const x)) = SubVessel k v Identity
  crop (SubVessel q) (SubVessel r) = SubVessel (crop q r)

instance (Ord k, Semigroup (v Identity), View v ) => Query (SubVessel k v Proxy) where
  type QueryResult (SubVessel k v Proxy) = SubVessel k v Identity
  crop (SubVessel q) (SubVessel r) = SubVessel (crop q r)

instance
    ( Ord k
    , View v
    , Query (Vessel (SubVesselKey k v) g)
    , Semigroup (v (Compose c (VesselLeafWrapper (QueryResult (Vessel (SubVesselKey k v) g)))))
    )
    => Query (SubVessel k v (Compose c (g :: * -> *))) where
  type QueryResult (SubVessel k v (Compose c g)) = SubVessel k v
    (Compose c (VesselLeafWrapper (QueryResult (Vessel (SubVesselKey k v) g))))
  crop (SubVessel q) (SubVessel r) = SubVessel (crop q r)


traverseSubVessel :: (Ord k, View v, Applicative m) => (k -> v g -> m (v h)) -> SubVessel k v g -> m (SubVessel k v h)
traverseSubVessel f (SubVessel x) = SubVessel <$> traverseWithKeyV (\(SubVesselKey k) -> f k) x

singletonSubVessel :: forall k f v . View v => k -> v f -> SubVessel k v f
singletonSubVessel k f = SubVessel $ singletonV @v @(SubVesselKey k v) (SubVesselKey k :: SubVesselKey k v v ) f

lookupSubVessel :: (Ord k) => k -> SubVessel k v f -> Maybe (v f)
lookupSubVessel k = lookupV (SubVesselKey k) . unSubVessel

subVesselFromKeys :: (Ord k, View v) => (k -> v f) -> Set k -> SubVessel k v f
subVesselFromKeys f ks = SubVessel $ fromListV $ fmap (\k -> SubVesselKey k :~> f k) $ toList ks

type instance ViewQueryResult (SubVessel k v g) = SubVessel k v (ViewQueryResult g)

subVessel :: (Ord k, View v, ViewQueryResult (v g) ~ v (ViewQueryResult g)) => k -> ViewMorphism (v g) (SubVessel k v g)
subVessel k = ViewMorphism
  { _viewMorphism_mapQuery = singletonSubVessel k
  , _viewMorphism_mapQueryResult = lookupSubVessel k
  }

