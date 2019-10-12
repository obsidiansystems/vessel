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

module Data.Vessel.Vessel where

import Control.Arrow ((***))
import Control.Monad
import Data.Aeson
import Data.Some (Some)
import Data.Constraint.Extras
import Data.Functor.Identity
import Data.Functor.Const
import Data.Proxy
import Data.Dependent.Sum
import Data.Dependent.Sum.Orphans ()
import Data.Constraint.Forall
import Data.Dependent.Map.Monoidal (MonoidalDMap(..))
import Data.Dependent.Map.Internal (DMap (..))
import Data.Foldable hiding (null)
import qualified Data.Dependent.Map.Monoidal as DMap
import Data.GADT.Compare
import Data.GADT.Show
import Data.Witherable
import Data.Vessel.Internal
import GHC.Generics
import Reflex.Query.Class
import Reflex.Patch (Group(..), Additive)
import Data.Functor.Compose
import Data.Align
import qualified Data.Dependent.Map as DMap'
import Data.Maybe (fromMaybe)
import Data.These

import Data.Vessel.Class
import Data.Vessel.DependentMap

------- Vessel -------

-- | This type is a container for storing an arbitrary collection of functor-parametric container types of the sort
-- discussed above, keyed by a GADT whose index will specify which sort of container goes in each position.
--
-- Ordinary types with values have kind *
-- Functors have kind * -> *
-- Containers taking a functor as a parameter then have kind (* -> *) -> *
-- The keys of a vessel are indexed by a functor-parametric container type, so they have kind ((* -> *) -> *) -> *
-- Vessel itself, for any such key type, produces a functor-parametric container, so it has kind
-- (((* -> *) -> *) -> *) -> (* -> *) -> *
-- Law: None of the items in the Vessel's MonoidalDMap are nullV
newtype Vessel (k :: ((* -> *) -> *) -> *) (g :: * -> *) = Vessel { unVessel :: MonoidalDMap k (FlipAp g) }
  deriving (Generic)

deriving instance (GCompare k, Has' Eq k (FlipAp g)) => Eq (Vessel k g)

deriving instance (ForallF Show k, GShow k, Has' Show k (FlipAp g)) => Show (Vessel k g)

-- TODO: Ord, Read, Show

instance (Has View k, GCompare k, Has' Semigroup k (FlipAp Identity)) => Query (Vessel k (Const x)) where
  type QueryResult (Vessel k (Const x)) = Vessel k Identity
  crop q r = fromMaybe emptyV $ cropV (\_ a -> a) q r --TODO

instance (Has View k, GCompare k, Has' Semigroup k (FlipAp Identity)) => Query (Vessel k Proxy) where
  type QueryResult (Vessel k Proxy) = Vessel k Identity
  crop q r = fromMaybe emptyV $ cropV (\_ a -> a) q r --TODO


instance (GCompare k, ForallF ToJSON k, HasV ToJSON k g) => ToJSON (Vessel k g) where
  toJSON v = toJSON (toListV v)

instance (GCompare k, FromJSON (Some k), HasV FromJSON k g, Has View k) => FromJSON (Vessel k g) where
  parseJSON x = fmap fromListV (parseJSON x)

-- TODO: figure out how to write a single instance for the case of Compose which depends on a Query instance for the right hand
-- composed functor... and/or let's replace Query with something more appropriate since it's pretty uniform what we want the crop
-- function to be all the time now.

type family VesselLeafWrapper v where
  VesselLeafWrapper (Vessel k g) = g

instance ( Has View k
         , GCompare k
         , Has' Semigroup k (FlipAp (Compose c (VesselLeafWrapper (QueryResult (Vessel k g)))))
         , Query (Vessel k g) )
        => Query (Vessel k (Compose c g)) where
  type QueryResult (Vessel k (Compose c g)) = Vessel k (Compose c (VesselLeafWrapper (QueryResult (Vessel k g))))
  crop q r = fromMaybe emptyV $ cropV (\_ a -> a) q r

instance (Has' Semigroup k (FlipAp g), GCompare k, Has View k) => Semigroup (Vessel k g) where
  Vessel m <> Vessel n = Vessel $ filterNullFlipAps $ m <> n

instance (Has' Semigroup k (FlipAp g), GCompare k, Has View k) => Monoid (Vessel k g) where
  mempty = Vessel DMap.empty
  mappend = (<>)

instance (Has' Semigroup k (FlipAp g), Has' Group k (FlipAp g), GCompare k, Has View k) => Group (Vessel k g) where
  negateG (Vessel m) = Vessel (negateG m) --TODO: Do we know that nullV can't be the result of negateG?

instance (Has' Additive k (FlipAp g), Has' Semigroup k (FlipAp g), GCompare k, Has View k) => Additive (Vessel k g)

------- The View instance for Vessel itself --------

instance (Has View k, GCompare k) => View (Vessel k) where
  cropV :: (forall a. s a -> i a -> r a) -> Vessel k s -> Vessel k i -> Maybe (Vessel k r)
  cropV f sv iv = collapseNullV $ intersectionMaybeWithKeyV (\k s i -> has @View k (cropV f s i)) sv iv
  nullV :: Vessel k i -> Bool
  nullV (Vessel m) = DMap.null m
  mapV :: (forall a. f a -> g a) -> Vessel k f -> Vessel k g
  mapV f (Vessel m) = Vessel (DMap.mapWithKey (\k (FlipAp v) -> has @View k $ FlipAp (mapV f v)) m)
  traverseV :: (Applicative m) => (forall a. f a -> m (g a)) -> Vessel k f -> m (Vessel k g)
  traverseV f m = traverseWithKeyV (\k v -> has @View k $ traverseV f v) m
  condenseV :: (Foldable t, Filterable t, Functor t)
            => t (Vessel k g)
            -> Vessel k (Compose t g)
  condenseV col = condenseV' folded col
    where folded = fold $ fmap (unMonoidalDMap . unVessel) col
  disperseV :: (Align t) => Vessel k (Compose t g) -> t (Vessel k g)
  disperseV row = case findPivotD (unMonoidalDMap (unVessel row)) of
    NoneD -> nil
    OneD k (FlipAp v) -> has @View k $ fmap (singletonV k) (disperseV v)
    SplitD pivot _l _r -> uncurry (alignWith (mergeThese unionDistinctAscV)) $
      disperseV *** disperseV $ has @View pivot $ splitLTV pivot row
  mapMaybeV f (Vessel (MonoidalDMap m)) = collapseNullV $ Vessel $ MonoidalDMap $
    DMap'.mapMaybeWithKey (\k (FlipAp v) -> has @View k $ FlipAp <$> mapMaybeV f v) m
  alignWithMaybeV (f :: forall a. These (f a) (g a) -> Maybe (h a)) (Vessel as) (Vessel bs) = collapseNullV $ Vessel $
    let g :: forall v. k v -> These (FlipAp f v) (FlipAp g v) -> Maybe (FlipAp h v)
        g k = has @View k $ fmap FlipAp . \case
          This (FlipAp a) -> mapMaybeV (f . This) a
          That (FlipAp b) -> mapMaybeV (f . That) b
          These (FlipAp a) (FlipAp b) -> alignWithMaybeV f a b
    in alignWithKeyMaybeMonoidalDMap g as bs
  alignWithV (f :: forall a. These (f a) (g a) -> h a) (Vessel as) (Vessel bs) = Vessel $
    let g :: forall v. k v -> These (FlipAp f v) (FlipAp g v) -> FlipAp h v
        g k = has @View k $ FlipAp . \case
          This (FlipAp a) -> mapV (f . This) a
          That (FlipAp b) -> mapV (f . That) b
          These (FlipAp a) (FlipAp b) -> alignWithV f a b
    in alignWithKeyMonoidalDMap g as bs

instance (Has View k, GCompare k) => EmptyView (Vessel k) where
  emptyV = Vessel DMap.empty

toListV :: Vessel k g -> [VSum k g]
toListV (Vessel m) = fmap (\(k :=> FlipAp v) -> k :~> v) (DMap.toList m)

fromListV :: (GCompare k, Has View k) => [VSum k g] -> Vessel k g
fromListV vs = Vessel $
  DMap.fromListWithKey (\_ _ v -> v) $
  mapMaybe (\(k :~> v) -> has @View k $ if nullV v then Nothing else Just $ k :=> FlipAp v) vs

intersectionMaybeWithKeyV :: (GCompare k, Has View k) => (forall v. View v => k v -> v g -> v g' -> Maybe (v h)) -> Vessel k g -> Vessel k g' -> Vessel k h
intersectionMaybeWithKeyV f (Vessel m) (Vessel m') = Vessel $
  filterNullFlipAps $
  intersectionDMapMaybeWithKey (\k (FlipAp x) (FlipAp y) -> has @View k $ FlipAp <$> f k x y) m m'

traverseWithKeyV :: (GCompare k, Has View k, Applicative m) => (forall v. View v => k v -> v g -> m (v h)) -> Vessel k g -> m (Vessel k h)
traverseWithKeyV f (Vessel x) = Vessel . filterNullFlipAps <$> DMap.traverseWithKey (\k (FlipAp v) -> has @View k $ FlipAp <$> f k v) x

traverseWithKeyV_ :: (GCompare k, Has View k, Applicative m) => (forall v. View v => k v -> v g -> m ()) -> Vessel k g -> m ()
traverseWithKeyV_ f (Vessel x) = void $ DMap.traverseWithKey (\k (FlipAp v) -> has @View k $ Const () <$ f k v) x

buildV :: (GCompare k, Has View k, Applicative m) => Vessel k g -> (forall v. k v -> v g -> m (v h)) -> m (Vessel k h)
buildV v f = traverseWithKeyV f v

intersectionWithKeyV :: (GCompare k, Has View k) => (forall v. View v => k v -> v g -> v g' -> v h) -> Vessel k g -> Vessel k g' -> Vessel k h
intersectionWithKeyV f (Vessel m) (Vessel m') = Vessel $
  filterNullFlipAps $
  DMap.intersectionWithKey (\k (FlipAp x) (FlipAp y) -> has @View k $ FlipAp (f k x y)) m m'

------- Operations on Vessel -------

singletonV :: View v => k v -> v g -> Vessel k g
singletonV k v = Vessel $ if nullV v then DMap.empty else DMap.singleton k (FlipAp v)

lookupV :: (GCompare k) => k v -> Vessel k g -> Maybe (v g)
lookupV k (Vessel m) = unFlipAp <$> DMap.lookup k m

mapMaybeWithKeyV :: (GCompare k, Has View k) => (forall v. View v => k v -> v g -> Maybe (v g')) -> Vessel k g -> Vessel k g'
mapMaybeWithKeyV f (Vessel m) = Vessel $ DMap.mapMaybeWithKey (\k (FlipAp x) -> has @View k $ FlipAp <$> (collapseNullV =<< f k x)) m

--TODO: Upstream
intersectionDMapMaybeWithKey :: GCompare k => (forall x. k x -> a x -> b x -> Maybe (c x)) -> MonoidalDMap k a -> MonoidalDMap k b -> MonoidalDMap k c
intersectionDMapMaybeWithKey f a b = DMap.mapMaybeWithKey (\_ -> getCompose) $ DMap.intersectionWithKey (\k x y -> Compose $ f k x y) a b

------- Instances for Vessel -------
condenseV' :: forall k t g.
              ( Has View k, GCompare k, Foldable t, Filterable t, Functor t)
           => DMap k (FlipAp g)
           -> t (Vessel k g)
           -> Vessel k (Compose t g)
condenseV' folded col =
  case findPivotD folded of
    NoneD -> emptyV
    OneD (k :: k v) _ -> has @View k $ singletonV k (condenseV $ mapMaybe (lookupV k) col)
    SplitD pivot l r -> uncurry unionDistinctAscV $ (condenseV' l *** condenseV' r) $ has @View pivot $ splitV pivot col

unionDistinctAscV :: (GCompare k) => Vessel k g -> Vessel k g -> Vessel k g
unionDistinctAscV (Vessel l) (Vessel r) = Vessel $ DMap.unionWithKey (\_ x _ -> x) l r

splitV :: forall k t g v. (GCompare k, View v, Filterable t)
       => k v -> t (Vessel k g) -> (t (Vessel k g), t (Vessel k g))
splitV pivot col = unalignProperly $ mapMaybe (splitOneV pivot) col

splitOneV :: (GCompare k, View v) => k v -> Vessel k g -> Maybe (These (Vessel k g) (Vessel k g))
splitOneV pivot m =
  let (l@(Vessel l'), r@(Vessel r')) = splitLTV pivot m
  in case (DMap.null l', DMap.null r') of
    (True, True) -> Nothing
    (False, True) -> Just $ This l
    (True, False) -> Just $ That r
    (False, False) -> Just $ These l r

splitLTV :: (GCompare k, View v) => k v -> Vessel k g -> (Vessel k g, Vessel k g)
splitLTV k (Vessel m) = case DMap.splitLookup k m of
  (l, Just (FlipAp v), r) | not $ nullV v -> (Vessel (DMap.insert k (FlipAp v) l), Vessel r)
  (l, _, r) -> (Vessel l, Vessel r)

