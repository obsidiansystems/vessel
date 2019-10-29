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

module Data.Vessel.Map where

import Data.Aeson
import Data.Align
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Map.Monoidal (MonoidalMap (..))
import Reflex.Patch (Group(..), Additive)
import GHC.Generics
import qualified Data.Map.Monoidal as Map
import qualified Data.Map as Map'
import Data.Set (Set)

import Data.Vessel.Class
import Data.Vessel.Selectable
import Data.Vessel.Disperse
import Data.Vessel.ViewMorphism

-- | A functor-indexed container corresponding to Map k v.
newtype MapV k v g = MapV { unMapV :: MonoidalMap k (g v) }
  deriving (Eq, Ord, Show, Read, Semigroup, Monoid, Group, Additive, Generic)

instance (Ord k) => View (MapV k v) where
  cropV f (MapV s) (MapV i) = collapseNullV $ MapV (Map.intersectionWithKey (\_ x y -> f x y) s i)
  nullV (MapV m) = Map.null m
  condenseV m = MapV . fmap Compose . disperse . fmap unMapV $ m
  disperseV (MapV m) = fmap MapV . condense . fmap getCompose $ m
  mapV f (MapV m) = MapV $ Map.map f m
  traverseV f (MapV m) = MapV <$> traverse f m
  mapMaybeV f (MapV m) = collapseNullV $ MapV $ Map.mapMaybe f m
  alignWithMaybeV f (MapV (MonoidalMap a)) (MapV (MonoidalMap b)) = collapseNullV $ MapV $ MonoidalMap $ Map'.mapMaybe id $ alignWith f a b
  alignWithV f (MapV (MonoidalMap a)) (MapV (MonoidalMap b)) = MapV $ MonoidalMap $ alignWith f a b

instance (Ord k) => EmptyView (MapV k v) where
  emptyV = MapV Map.empty

instance (ToJSON k, ToJSON (g v), Ord k) => ToJSON (MapV k v g) where
  toJSON = toJSON . Map.toList . unMapV

instance (FromJSON k, FromJSON (g v), Ord k) => FromJSON (MapV k v g) where
  parseJSON r = do
    res <- parseJSON r
    fmap MapV $ sequence $ Map.fromListWithKey (\_ _ -> fail "duplicate key in JSON deserialization of MapV") $ fmap (fmap return) res

instance (Ord k) => Selectable (MapV k v) (Set k) where
  type Selection (MapV k v) (Set k) = MonoidalMap k v
  selector p s = MapV (Map.fromSet (const p) s)
  selection _ (MapV m) = fmap (\(Identity a) -> a) m

instance Ord k => Selectable (MapV k v) (Identity k) where
  type Selection (MapV k v) (Identity k) = Maybe v
  selector p (Identity k) = MapV (Map.singleton k p)
  selection (Identity k) (MapV m) = Map.lookup k $ fmap (\(Identity a) -> a) m

singletonMapV :: k -> g v -> MapV k v g
singletonMapV k v = MapV $ Map.singleton k v

lookupMapV :: Ord k => k -> MapV k v g -> Maybe (g v)
lookupMapV k (MapV xs) = Map.lookup k xs

type instance ViewQueryResult (MapV k v g) = MapV k v (ViewQueryResult g)
mapVMorphism
  :: ( Ord k , ViewQueryResult (g v) ~ ViewQueryResult g v)
  => k -> ViewMorphism (g v) (MapV k v g)
mapVMorphism k = ViewMorphism
  { _viewMorphism_mapQuery = singletonMapV k
  , _viewMorphism_mapQueryResult = lookupMapV k
  , _viewMorphism_buildResult = singletonMapV k
  }

-- | A gadget to "traverse" over all of the keys in a MapV in one step
handleMapVSelector
  :: forall a f g k m.
  ( Ord k, Functor m )
  => (forall x. x -> f x -> g x)
  -> (Set k -> m (MonoidalMap k a))
  ->    MapV k a f
  -> m (MapV k a g)
handleMapVSelector k f (MapV xs) = (\ys -> MapV $ Map.intersectionWith k ys xs) <$> f (Map.keysSet xs)
