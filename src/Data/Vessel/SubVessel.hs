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

import Control.Applicative
import Data.Aeson
import Data.Constraint
import Data.Constraint.Extras
import Data.Dependent.Map.Monoidal (MonoidalDMap(..))
import Data.Dependent.Sum (DSum(..))
import Data.Foldable
import Data.Functor.Compose
import Data.Functor.Identity
import Data.GADT.Compare
import Data.GADT.Show
import Data.Map.Monoidal (MonoidalMap(..))
import Data.Proxy
import Data.Set (Set)
import Data.Some (Some(Some))
import Data.Type.Equality
import GHC.Generics
import Data.Patch (Group(..), Additive)
import Reflex.Query.Class
import qualified Data.Dependent.Map as DMap'
import qualified Data.Dependent.Map.Monoidal as DMap
import qualified Data.Map.Monoidal as Map

import Data.Vessel.Class hiding (empty)
import Data.Vessel.Vessel
import Data.Vessel.Internal
import Data.Vessel.ViewMorphism

data SubVesselKey k (f :: (* -> *) -> *) (g :: (* -> *) -> *) where
  SubVesselKey :: k -> SubVesselKey k f f
deriving instance Show k => Show (SubVesselKey k f g)
instance Show k => GShow (SubVesselKey k f) where gshowsPrec = showsPrec

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

-- | Something between MapV and Vessel, where the keys are simple values, but the values are full views.
--
-- TODO: this representation has the advantage that all of it's instances come "free", but the mostly "right" representation is probably
-- ... Vessel v (Compose (MonoidalMap k) f)
newtype SubVessel (k :: *)  (v :: (* -> *) -> *) (f :: * -> *) = SubVessel { unSubVessel :: Vessel (SubVesselKey k v) f }
  deriving (FromJSON, ToJSON, Semigroup, Monoid, Generic, Group, Additive, Eq)

deriving instance (Show k, Show (v f)) => Show (SubVessel k v f)

-- slightly nicer unwrapper compared to unSubVessel
getSubVessel :: Ord k => SubVessel k v f -> MonoidalMap k (v f)
getSubVessel = Map.fromListWith (error "getSubVessel:collision") . fmap (\(SubVesselKey k :~> v) -> (k, v)) . toListV . unSubVessel

mkSubVessel :: Ord k => MonoidalMap k (v f) -> SubVessel k v f
mkSubVessel = SubVessel . Vessel . MonoidalDMap . DMap'.fromList . fmap (\(k, v) -> (SubVesselKey k :=> FlipAp v)) . Map.toList


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

subVessel :: (Ord k, View v, ViewQueryResult (v g) ~ v (ViewQueryResult g), Alternative n, Applicative m) => k -> ViewMorphism m n (v g) (SubVessel k v g)
subVessel k = ViewMorphism (toSubVessel k) (fromSubVessel k)

toSubVessel :: (Ord k, Applicative m, Alternative n, View v, ViewQueryResult (v g) ~ v (ViewQueryResult g)) => k -> ViewHalfMorphism m n (v g) (SubVessel k v g)
toSubVessel k = ViewHalfMorphism
  { _viewMorphism_mapQuery = pure . singletonSubVessel k
  , _viewMorphism_mapQueryResult = maybe empty pure . lookupSubVessel k
  }

fromSubVessel :: (Ord k, Alternative m, Applicative n, View v, ViewQueryResult (v g) ~ v (ViewQueryResult g)) => k -> ViewHalfMorphism m n (SubVessel k v g) (v g)
fromSubVessel k = ViewHalfMorphism
  { _viewMorphism_mapQuery = maybe empty pure . lookupSubVessel k
  , _viewMorphism_mapQueryResult = pure . singletonSubVessel k
  }


subVesselWildcard
  ::
  ( Ord k
  , View v, ViewQueryResult (v g) ~ v (ViewQueryResult g)
  , Semigroup (v g), Semigroup (v (ViewQueryResult g))
  , Alternative n
  , Applicative m
  ) => ViewMorphism m n (v g) (SubVessel k v g)
subVesselWildcard = ViewMorphism toSubVesselWildcard fromSubVesselWildcard

toSubVesselWildcard
  ::
  ( Ord k
  , Applicative m, Alternative n
  , View v, ViewQueryResult (v g) ~ v (ViewQueryResult g)
  , Semigroup (v (ViewQueryResult g))
  ) => ViewHalfMorphism m n (v g) (SubVessel k v g)
toSubVesselWildcard = ViewHalfMorphism
  { _viewMorphism_mapQuery = const $ pure $ SubVessel $ Vessel $ DMap.empty
  , _viewMorphism_mapQueryResult = maybe empty pure . foldMap Just . getSubVessel
  }

fromSubVesselWildcard
  ::
  ( Ord k
  , Alternative m, Applicative n
  , Semigroup (v g)
  ) => ViewHalfMorphism m n (SubVessel k v g) (v g)
fromSubVesselWildcard = ViewHalfMorphism
  { _viewMorphism_mapQuery = maybe empty pure . foldMap Just . getSubVessel
  , _viewMorphism_mapQueryResult = const $ pure $ SubVessel $ Vessel $ DMap.empty
  }

subVessels ::
  ( Ord k, Applicative m, View v , Alternative n
  , ViewQueryResult (v g) ~ v (ViewQueryResult g)
  , Monoid (n (v g)) , Monoid (n (v (ViewQueryResult g)))
  ) => Set k -> ViewMorphism m n (v g) (SubVessel k v g)
subVessels k = ViewMorphism (toSubVessels k) (fromSubVessels k)

toSubVessels ::
  ( Ord k, Applicative m, View v , Alternative n
  , ViewQueryResult (v g) ~ v (ViewQueryResult g)
  , Monoid (n (v (ViewQueryResult g)))
  ) => Set k -> ViewHalfMorphism m n (v g) (SubVessel k v g)
toSubVessels k = ViewHalfMorphism
  { _viewMorphism_mapQuery = pure . flip subVesselFromKeys k . const
  , _viewMorphism_mapQueryResult = fold . leftOuterJoin_ empty k . fmap pure . getSubVessel
  }

fromSubVessels ::
  ( Ord k, Applicative m, View v , Alternative n
  , ViewQueryResult (v g) ~ v (ViewQueryResult g)
  , Monoid (n (v g))
  ) => Set k -> ViewHalfMorphism n m (SubVessel k v g) (v g)
fromSubVessels k = ViewHalfMorphism
  { _viewMorphism_mapQuery = fold . leftOuterJoin_ empty k . fmap pure . getSubVessel
  , _viewMorphism_mapQueryResult = pure . flip subVesselFromKeys k . const
  }


mapMaybeWithKeySubVessel :: forall k v (g :: * -> *) (g' :: * -> *) . (View v, Ord k) => (k -> v g -> Maybe (v g')) -> SubVessel k v g -> SubVessel k v g'
mapMaybeWithKeySubVessel f (SubVessel xs) = SubVessel (mapMaybeWithKeyV @(SubVesselKey k v) f' xs)
  where
    f' :: forall x . SubVesselKey k v x -> x g -> Maybe (x g')
    f' (SubVesselKey k) = f k


uncurrySubVessel :: (Ord k1, Ord k2) => MonoidalMap k1 (SubVessel k2 v f) -> SubVessel (k1, k2) v f
uncurrySubVessel xs = mkSubVessel $ uncurryMMap $ fmap getSubVessel xs

currySubVessel :: (Ord k1, Ord k2) => SubVessel (k1, k2) v f -> MonoidalMap k1 (SubVessel k2 v f)
currySubVessel xs = fmap mkSubVessel $ curryMMap $ getSubVessel xs

-- | the instance for Filterable (MonoidalMap k) is not defined anyplace conveninent, this sidesteps it for this particular case.
condenseVMMap :: forall k v g. View v => MonoidalMap k (v g) -> v (Compose (MonoidalMap k) g)
condenseVMMap = mapV (Compose . MonoidalMap . getCompose) . condenseV . getMonoidalMap

-- | A gadget to "traverse" over all of the keys in a SubVessel in one step
handleSubVesselSelector
  ::  forall k m tag (f :: * -> *) (g :: * -> *).
  ( Ord k, Applicative m, Has View tag, GCompare tag )
  => (forall v.  tag v
             ->    MonoidalMap k (v f)
             -> m (MonoidalMap k (v g)))
  ->    SubVessel k (Vessel tag) f
  -> m (SubVessel k (Vessel tag) g)
handleSubVesselSelector f xs = (\y -> mkSubVessel $ disperseV y) <$> traverseWithKeyV f' (condenseVMMap $ getSubVessel xs)
  where
    f' :: forall v.  tag v
       ->    v (Compose (MonoidalMap k) f)
       -> m (v (Compose (MonoidalMap k) g))
    f' tag xs' = has @View tag $ condenseVMMap <$> f tag (disperseV xs')

-- | A gadget to "traverse" over all of the keys in a SubVessel, aligned to the keys nested inside a deeper Map, in one step
handleSubSubVesselSelector
  :: (Ord k1, Ord k2, Applicative m, Has View tag, GCompare tag)
  => (forall v. tag v -> MonoidalMap (k1, k2) (v f) -> m (MonoidalMap (k1, k2) (v g)))
  ->    MonoidalMap k1 (SubVessel k2 (Vessel tag) f)
  -> m (MonoidalMap k1 (SubVessel k2 (Vessel tag) g))
handleSubSubVesselSelector f xs = currySubVessel <$> handleSubVesselSelector f (uncurrySubVessel xs)

instance (Ord k, View v) => EmptyView (SubVessel k v) where
  emptyV = SubVessel emptyV

