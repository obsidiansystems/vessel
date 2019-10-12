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

module Data.Vessel.SubVessel where


import Data.Aeson
import Data.Constraint
import Data.Constraint.Extras
import Data.GADT.Compare
import Data.Vessel.Class
import Reflex.Query.Class
import Data.Some (Some(Some))
import Data.Vessel.Vessel
import GHC.Generics
import Reflex.Patch (Group(..), Additive)
import Data.Functor.Identity
import Data.Functor.Const

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

instance (Ord k, View v) => View (SubVessel k v)

instance (Ord k, Semigroup (v Identity), View v) => Query (SubVessel k v (Const x)) where
  type QueryResult (SubVessel k v (Const x)) = SubVessel k v Identity
  crop (SubVessel q) (SubVessel r) = SubVessel (crop q r)

traverseSubVessel :: (Ord k, View v, Applicative m) => (k -> v g -> m (v h)) -> SubVessel k v g -> m (SubVessel k v h)
traverseSubVessel f (SubVessel x) = SubVessel <$> traverseWithKeyV (\(SubVesselKey k) -> f k) x

singletonSubVessel :: forall k f v . View v => k -> v f -> SubVessel k v f
singletonSubVessel k f = SubVessel $ singletonV @v @(SubVesselKey k v) (SubVesselKey k :: SubVesselKey k v v ) f

lookupSubVessel :: (Ord k) => k -> SubVessel k v f -> Maybe (v f)
lookupSubVessel k = lookupV (SubVesselKey k) . unSubVessel
