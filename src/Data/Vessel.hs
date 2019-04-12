{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
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
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -fno-warn-orphans #-} -- TODO Upstream orphans

module Data.Vessel
  ( Vessel(..)
  , View(..)
  , Selectable(..)
  , FlipAp(..)
  , IdentityV(..)
  , SingleV(..)
  , MapV(..)
  , DMapV(..)
  , emptyV
  , singletonV
  , lookupV
  , buildV
  , mapMaybeWithKeyV
  , traverseWithKeyV
  , intersectionWithKeyV
  , mapDecomposedV
  , VSum (..)
  , toListV
  , fromListV
  , module Data.Proxy
  , module Data.Functor.Identity
  , module Data.Functor.Const
  , transposeView
  ) where

import Control.Arrow ((***))
import Control.Monad
import Data.Aeson
import Data.Align
import Data.Constraint.Extras
import Data.Constraint.Forall
import qualified Data.Dependent.Map as DMap'
import Data.Dependent.Map.Internal (DMap (..))
import Data.Dependent.Map.Monoidal (MonoidalDMap(..))
import qualified Data.Dependent.Map.Monoidal as DMap
import Data.Dependent.Sum
import Data.Dependent.Sum.Orphans ()
import Data.Foldable hiding (null)
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.GADT.Compare
import Data.Map.Monoidal (MonoidalMap)
import qualified Data.Map.Monoidal as Map
import Data.Maybe
import Data.Proxy
import Data.Semigroup
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Some as Some
import Data.Some hiding (This)
import Data.These
import GHC.Generics (Generic)
import Prelude hiding (lookup, map, null)
import Reflex (Group(..), Additive, Query(..), QueryMorphism(..), FunctorMaybe(..))

------- The View Class -------

-- | Our containers are parameterised by a choice of functor to apply at the leaves of their
-- structure. By applying them to Identity, we obtain ordinary containers for data, called "views".
-- By applying them to Proxy, we obtain what are effectively blank forms to be filled in, called
-- "queries" or "view selectors". By using a functor such as Map k, information about many queries
-- or their results may be aggregated together into a single container.
--
-- This class codifies the operations we need to be able to perform on these container types in
-- order to transpose various Map-like structures into and out of them.
--
-- This is done for the purposes of, on the one hand collecting many users' view selectors into a
-- single aggregated selector containing information about who is interested in each part (condenseV),
-- and on the other hand, taking the resulting aggregated views and splitting them into a Map of
-- views for each user (disperseV).
--
-- It also specifies the cropV operation which restricts a view to a particular selection, as well
-- as operations for mapping functions over all the leaves of the container.
class View (v :: (* -> *) -> *) where
  -- | Transpose a sufficiently-Map-like structure into a container, effectively aggregating
  -- many structures into a single one containing information about which keys each part of it
  -- came from originally.
  condenseV :: (Foldable t, FunctorMaybe t, Functor t) => t (v g) -> v (Compose t g)
  -- | Transpose a sufficiently-Map-like structure out of a container, the inverse of condenseV.
  disperseV :: (Align t) => v (Compose t g) -> t (v g)
  -- TODO: Decide whether mapV and traverseV are actually a good idea to provide.
  -- They may actually help people write operations which are inefficient.
  -- | Given a structure specifying a query, and a structure representing a view of data,
  -- restrict the view to only those parts which satisfy the query. (Essentially intersection of Maps.)
  cropV :: (forall a. s a -> i a -> r a) -> v s -> v i -> v r
  -- | Given a structure specifying a new query, and a structure representing an old query,
  -- restrict the new query to only those parts which are new. (Essentially difference of Maps.)
  subtractV :: (forall a. s a -> s a -> Maybe (s a)) -> v s -> v s -> Maybe (v s)
  -- | We also want a way to determine if the container is empty, because shipping empty containers
  -- around is a bad idea.
  nullV :: v i -> Bool
  -- | Map a natural transformation over all the leaves of a container, changing the functor which
  -- has been applied.
  mapV :: (forall a. f a -> g a) -> v f -> v g
  -- | Traverse over the leaves of a container.
  traverseV :: (Applicative m) => (forall a. f a -> m (g a)) -> v f -> m (v g)
  -- | Map over all the leaves of a container, keeping only the 'Just' results
  -- and returing 'Nothing' if no leaves are kept.
  mapMaybeV :: (forall a. f a -> Maybe (g a)) -> v f -> Maybe (v g)

-- | A main point of the View class is to be able to produce this QueryMorphism.
transposeView
  :: ( View v
     , Foldable t
     , FunctorMaybe t
     , Functor t
     , Align t
     , QueryResult (t (v g)) ~ (t (v g'))
     , QueryResult (v (Compose t g)) ~ v (Compose t g')
     , Monoid (v g)
     , Monoid (v (Compose t g))
     )
  => QueryMorphism (t (v g)) (v (Compose t g))
transposeView = QueryMorphism
  { _queryMorphism_mapQuery = condenseV -- aggregate queries.
  , _queryMorphism_mapQueryResult = disperseV -- individualise results.
  }

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
newtype Vessel (k :: ((* -> *) -> *) -> *) (g :: * -> *) = Vessel { unVessel :: MonoidalDMap k (FlipAp g) }
  deriving (Generic)

newtype FlipAp (g :: k) (v :: k -> *) = FlipAp { unFlipAp :: v g }
  deriving (Eq, Ord, Show)

deriving instance (GCompare k, Has' Eq k (FlipAp g)) => Eq (Vessel k g)

-- TODO: Ord, Read, Show

instance (Has View k, GCompare k, Has' Semigroup k (FlipAp Identity)) => Query (Vessel k (Const x)) where
  type QueryResult (Vessel k (Const x)) = Vessel k Identity
  crop = cropV (\_ a -> a)

instance (Has View k, GCompare k, Has' Semigroup k (FlipAp Identity)) => Query (Vessel k Proxy) where
  type QueryResult (Vessel k Proxy) = Vessel k Identity
  crop = cropV (\_ a -> a)

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
  crop = cropV (\_ a -> a)

-- A single Vessel key/value pair, essentially a choice of container type, together with a corresponding container.
data VSum (k :: ((* -> *) -> *) -> *) (g :: * -> *) = forall v. k v :~> v g

toListV :: Vessel k g -> [VSum k g]
toListV (Vessel m) = fmap (\(k :=> FlipAp v) -> k :~> v) (DMap.toList m)

fromListV :: (GCompare k) => [VSum k g] -> Vessel k g
fromListV vs = Vessel (DMap.fromListWithKey (\_ _ v -> v) $ fmap (\(k :~> v) -> k :=> FlipAp v) vs)

------- Serialisation -------

instance (ForallF ToJSON k, HasV ToJSON k g) => ToJSON (VSum k g) where
  toJSON ((k :: k v) :~> (v :: v g)) =
    toJSON ( whichever @ToJSON @k @v (toJSON k)
           , hasV @ToJSON @g k (toJSON v))

instance forall k g. (FromJSON (Some k), HasV FromJSON k g) => FromJSON (VSum k g) where
  parseJSON x = do
    (jk, jv) <- parseJSON x
    (Some.This k) <- parseJSON jk
    v <- hasV @FromJSON @g k (parseJSON jv)
    return (k :~> v)

instance (GCompare k, ForallF ToJSON k, HasV ToJSON k g) => ToJSON (Vessel k g) where
  toJSON v = toJSON (toListV v)

instance (GCompare k, FromJSON (Some k), HasV FromJSON k g) => FromJSON (Vessel k g) where
  parseJSON x = fmap fromListV (parseJSON x)

------- Simple structure components -------

-- | A functor-indexed container corresponding to Identity. (i.e. a single non-deletable item)
newtype IdentityV (a :: *) (g :: * -> *) = IdentityV { unIdentityV :: g a }
  deriving (Eq, Ord, Show, Read, Semigroup, Monoid, Group, Additive, Generic)

instance View (IdentityV a) where
  cropV f (IdentityV s) (IdentityV x) = IdentityV $ f s x
  subtractV f (IdentityV s) (IdentityV x) = IdentityV <$> f s x
  nullV _ = False
  condenseV m = IdentityV (Compose (fmap unIdentityV m))
  disperseV (IdentityV (Compose m)) = fmap IdentityV m
  mapV f (IdentityV x) = IdentityV (f x)
  traverseV f (IdentityV x) = IdentityV <$> f x
  mapMaybeV f (IdentityV x) = IdentityV <$> f x

instance ToJSON (g a) => ToJSON (IdentityV a g)

instance FromJSON (g a) => FromJSON (IdentityV a g)

-- | A functor-indexed container for a single deletable item.
newtype SingleV (a :: *) (g :: * -> *) = SingleV { unSingleV :: g (First (Maybe a)) }
  deriving (Generic)

deriving instance (Eq (g (First (Maybe a)))) => Eq (SingleV a g)
deriving instance (Ord (g (First (Maybe a)))) => Ord (SingleV a g)
deriving instance (Show (g (First (Maybe a)))) => Show (SingleV a g)
deriving instance (Read (g (First (Maybe a)))) => Read (SingleV a g)

instance (Semigroup (g (First (Maybe a)))) => Semigroup (SingleV a g) where
  (SingleV x) <> (SingleV y) = SingleV (x <> y)

instance (Monoid (g (First (Maybe a)))) => Monoid (SingleV a g) where
  mempty = SingleV mempty
  mappend (SingleV x) (SingleV y) = SingleV (mappend x y)

instance (Group (g (First (Maybe a)))) => Group (SingleV a g) where
  negateG (SingleV x) = SingleV (negateG x)

instance (Additive (g (First (Maybe a)))) => Additive (SingleV a g)

instance View (SingleV a) where
  cropV f (SingleV s) (SingleV i) = SingleV $ f s i
  subtractV f (SingleV s) (SingleV i) = SingleV <$> f s i
  nullV (SingleV _) = False
  condenseV :: (Foldable t, FunctorMaybe t, Functor t) => t (SingleV a g) -> SingleV a (Compose t g)
  condenseV m = SingleV . Compose $ fmap unSingleV m
  disperseV :: (Align t) => SingleV a (Compose t g) -> t (SingleV a g)
  disperseV (SingleV (Compose x)) = fmap SingleV x
  mapV :: (forall x. f x -> g x) -> SingleV a f -> SingleV a g
  mapV f (SingleV x) = SingleV $ f x
  traverseV :: (Applicative m) => (forall x. f x -> m (g x)) -> SingleV a f -> m (SingleV a g)
  traverseV f (SingleV x) = SingleV <$> f x
  mapMaybeV f (SingleV x) = SingleV <$> f x

instance ToJSON (g (First (Maybe a))) => ToJSON (SingleV a g)

instance FromJSON (g (First (Maybe a))) => FromJSON (SingleV a g)

-- | A functor-indexed container corresponding to Map k v.
newtype MapV k v g = MapV { unMapV :: MonoidalMap k (g v) }
  deriving (Eq, Ord, Show, Read, Semigroup, Monoid, Group, Additive, Generic)

instance (Ord k) => View (MapV k v) where
  cropV f (MapV s) (MapV i) = MapV (Map.intersectionWithKey (\_ x y -> f x y) s i)
  subtractV f (MapV s) (MapV i) = collapseNullV $ MapV (Map.differenceWithKey (\_ x y -> f x y) s i)
  nullV (MapV m) = Map.null m
  condenseV m = MapV . fmap Compose . disperse . fmap unMapV $ m
  disperseV (MapV m) = fmap MapV . condense . fmap getCompose $ m
  mapV f (MapV m) = MapV $ Map.map f m
  traverseV f (MapV m) = MapV <$> traverse f m
  mapMaybeV f (MapV m) = collapseNullV $ MapV $ Map.mapMaybe f m

instance (ToJSON k, ToJSON (g v), Ord k) => ToJSON (MapV k v g) where
  toJSON = toJSON . Map.toList . unMapV

instance (FromJSON k, FromJSON (g v), Ord k) => FromJSON (MapV k v g) where
  parseJSON r = do
    res <- parseJSON r
    fmap MapV $ sequence $ Map.fromListWithKey (\_ _ -> fail "duplicate key in JSON deserialization of MapV") $ fmap (fmap return) res

-- | A functor-indexed container corrresponding to DMap k v.
newtype DMapV (k :: * -> *) (v :: * -> *) g = DMapV { unDMapV :: MonoidalDMap k (Compose g v) }
  deriving (Eq, Ord, Read, Semigroup, Monoid, Group, Additive, Generic)

instance (Has' ToJSON k (Compose g v), ForallF ToJSON k) => ToJSON (DMapV k v g)

instance (Has' FromJSON k (Compose g v), FromJSON (Some k), GCompare k) => FromJSON (DMapV k v g)

deriving instance (ForallF Show k, Has' Show k (Compose g v)) => Show (DMapV k v g)

instance (GCompare k) => View (DMapV k v) where
  cropV f (DMapV s) (DMapV i) = DMapV (DMap.intersectionWithKey (\_ (Compose x) (Compose y) -> Compose $ f x y) s i)
  subtractV f (DMapV s) (DMapV i) = collapseNullV $ DMapV (DMap.differenceWithKey (\_ (Compose x) (Compose y) -> Compose <$> f x y) s i)
  nullV (DMapV m) = DMap.null m
  condenseV m = DMapV . DMap.map assocLCompose . condenseV . fmap unDMapV $ m
  disperseV (DMapV m) = fmap DMapV . disperseV . DMap.map assocRCompose $ m
  mapV f (DMapV m) = DMapV $ DMap.map (\(Compose x) -> Compose (f x)) m
  traverseV f (DMapV m) = DMapV <$> DMap.traverseWithKey (\_ (Compose x) -> Compose <$> f x) m
  mapMaybeV f (DMapV (MonoidalDMap m)) = collapseNullV $ DMapV $ MonoidalDMap $
    DMap'.mapMaybe (fmap Compose . f . getCompose) m

------- Selectable convenience class -------

-- A convenience class for producing and consuming functor-indexed containers.
class Selectable v k where
  -- | A more convenient type to use for extracting results.
  type Selection v k
  -- | Build a query given a suitable value for specifying what we're asking for.
  -- 'p' will typically be Proxy or Const SelectedCount.
  selector :: (forall a. p a) -> k -> v p
  -- | From a view, extract a more convenient type of value to use.
  selection :: k -> v Identity -> Selection v k

instance Selectable (IdentityV a) () where
  type Selection (IdentityV a) () = a
  selector p () = IdentityV p
  selection () (IdentityV (Identity a)) = a

instance Selectable (SingleV a) () where
  type Selection (SingleV a) () = Maybe a
  selector p () = SingleV p
  selection () (SingleV x) = getFirst . runIdentity $ x

instance (Ord k) => Selectable (MapV k v) (Set k) where
  type Selection (MapV k v) (Set k) = MonoidalMap k v
  selector p s = MapV (Map.fromSet (const p) s)
  selection _ (MapV m) = fmap (\(Identity a) -> a) m

instance Ord k => Selectable (MapV k v) (Identity k) where
  type Selection (MapV k v) (Identity k) = Maybe v
  selector p (Identity k) = MapV (Map.singleton k p)
  selection (Identity k) (MapV m) = Map.lookup k $ fmap (\(Identity a) -> a) m

instance (GCompare k) => Selectable (DMapV k v) (Set (Some k)) where
  type Selection (DMapV k v) (Set (Some k)) = MonoidalDMap k v
  selector p s = DMapV . DMap.fromListWithKey (\_ x _ -> x) $
    fmap (\(Some.This k) -> k :=> Compose p) (Set.toList s)
  selection _ (DMapV m) = DMap.map (\(Compose (Identity v)) -> v) m

------- Operations on Vessel -------

singletonV :: k v -> v g -> Vessel k g
singletonV k v = Vessel (DMap.singleton k (FlipAp v))

emptyV :: Vessel k g
emptyV = Vessel (DMap.empty)

lookupV :: (GCompare k) => k v -> Vessel k g -> Maybe (v g)
lookupV k (Vessel m) = unFlipAp <$> DMap.lookup k m

mapMaybeWithKeyV :: (GCompare k) => (forall v. k v -> v g -> Maybe (v g')) -> Vessel k g -> Vessel k g'
mapMaybeWithKeyV f (Vessel m) = Vessel $ DMap.mapMaybeWithKey (\k (FlipAp x) -> FlipAp <$> f k x) m

traverseWithKeyV :: (GCompare k, Applicative m) => (forall v. k v -> v g -> m (v h)) -> Vessel k g -> m (Vessel k h)
traverseWithKeyV f (Vessel x) = Vessel <$> DMap.traverseWithKey (\k (FlipAp v) -> FlipAp <$> f k v) x

buildV :: (GCompare k, Applicative m) => Vessel k g -> (forall v. k v -> v g -> m (v h)) -> m (Vessel k h)
buildV v f = traverseWithKeyV f v

intersectionWithKeyV :: (GCompare k) => (forall v. k v -> v g -> v g' -> v h) -> Vessel k g -> Vessel k g' -> Vessel k h
intersectionWithKeyV f (Vessel m) (Vessel m') = Vessel $
  DMap.intersectionWithKey (\k (FlipAp x) (FlipAp y) -> FlipAp (f k x y)) m m'

differenceWithKeyV :: (GCompare k) => (forall v. k v -> v g -> v g -> Maybe (v g)) -> Vessel k g -> Vessel k g -> Vessel k g
differenceWithKeyV f (Vessel m) (Vessel m') = Vessel $
  DMap.differenceWithKey (\k (FlipAp x) (FlipAp y) -> FlipAp <$> f k x y) m m'

------- Instances for FlipAp -------

instance Semigroup (v g) => Semigroup (FlipAp g v) where
  FlipAp x <> FlipAp y = FlipAp (x <> y)

instance Monoid (v g) => Monoid (FlipAp g v) where
  mempty = FlipAp mempty
  mappend (FlipAp x) (FlipAp y) = FlipAp (mappend x y)

instance Group (v g) => Group (FlipAp g v) where
  negateG (FlipAp x) = FlipAp (negateG x)

instance Additive (v g) => Additive (FlipAp g v)

------- Instances for Vessel -------

instance (Has' Semigroup k (FlipAp g), GCompare k) => Semigroup (Vessel k g) where
  Vessel m <> Vessel n = Vessel (m <> n)

instance (Has' Semigroup k (FlipAp g), GCompare k) => Monoid (Vessel k g) where
  mempty = Vessel (DMap.empty)
  mappend = (<>)

instance (Has' Semigroup k (FlipAp g), Has' Group k (FlipAp g), GCompare k) => Group (Vessel k g) where
  negateG (Vessel m) = Vessel (negateG m)

instance (Has' Additive k (FlipAp g), Has' Semigroup k (FlipAp g), GCompare k) => Additive (Vessel k g)

-- | Disperse is a simplified version of View for ordinary containers. This is used as a stepping stone to obtain the View instance for MapV.
class Disperse row where
  disperse :: (Foldable col, FunctorMaybe col, Functor col) => col (row a) -> row (col a)
  condense :: (Align col) => row (col a) -> col (row a)

instance Ord k => Disperse (MonoidalMap k) where
  disperse :: forall col a. (Foldable col, FunctorMaybe col, Functor col)
           => col (MonoidalMap k a)
           -> MonoidalMap k (col a)
  disperse col = disperse' (Map.MonoidalMap (fold (fmap Map.getMonoidalMap col))) col
    where
      disperse'
        :: MonoidalMap k a
        -> col (MonoidalMap k a)
        -> MonoidalMap k (col a)
      disperse' folded col' = case findPivot folded of
        None -> Map.MonoidalMap mempty
        One k _ -> Map.singleton k (fmapMaybe (Map.lookup k) col')
        Split pivot l r -> uncurry unionDistinctAsc $ (disperse' l *** disperse' r) $ split pivot col'
      split
        :: (Ord k, FunctorMaybe col)
        => k -> col (MonoidalMap k a)
        -> (col (MonoidalMap k a), col (MonoidalMap k a))
      split pivot col' = unalignProperly $ fmapMaybe (splitOne pivot) col'
      splitOne
        :: Ord k
        => k
        -> MonoidalMap k a
        -> Maybe (These (MonoidalMap k a) (MonoidalMap k a))
      splitOne pivot m =
        let (l, r) = splitLT pivot m
        in case (Map.null l, Map.null r) of
          (True, True) -> Nothing
          (False, True) -> Just $ This l
          (True, False) -> Just $ That r
          (False, False) -> Just $ These l r

  condense :: forall col a. (Align col)
           => MonoidalMap k (col a)
           -> col (MonoidalMap k a)
  condense row = case findPivot row of
    None -> nil
    One k v -> fmap (Map.singleton k) v
    Split pivot _l _r -> uncurry (alignWith (mergeThese unionDistinctAsc)) $ condense *** condense $ splitLT pivot row

data Pivot k a = None | One k a | Split k (MonoidalMap k a) (MonoidalMap k a)
  deriving (Eq, Ord, Show)

findPivot :: Ord k => MonoidalMap k a -> Pivot k a
findPivot m = case Map.splitRoot m of
  [] -> None
  [l,xm,r] -> case Map.toList xm of
      [(k,v)] | Map.null l && Map.null r -> One k v
              | otherwise -> Split k (Map.insert k v l) r
      _ -> errorMsg
  _ -> errorMsg
  where errorMsg = error "Data.Vessel.findPivot: unexpected result from Data.MonoidalMap.splitRoot (wrong version of monoidal-containers?)"

splitLT :: Ord k => k -> MonoidalMap k a -> (MonoidalMap k a, MonoidalMap k a)
splitLT k m = case Map.splitLookup k m of
  (l, Just v, r) -> (Map.insert k v l, r)
  (l, Nothing, r) -> (l, r)

unionDistinctAsc :: (Ord k) => MonoidalMap k a -> MonoidalMap k a -> MonoidalMap k a
unionDistinctAsc = Map.unionWith (\x _ -> x)

------- The View instance for MonoidalDMap -------

instance (GCompare k) => View (MonoidalDMap k) where
  cropV :: (forall a. s a -> i a -> r a) -> MonoidalDMap k s -> MonoidalDMap k i -> MonoidalDMap k r
  cropV f = DMap.intersectionWithKey (\_ s i -> f s i)

  subtractV :: (forall a. s a -> s a -> Maybe (s a)) -> MonoidalDMap k s -> MonoidalDMap k s -> Maybe (MonoidalDMap k s)
  subtractV f new old = collapseNullV $ DMap.differenceWithKey (\_ s i -> f s i) new old

  nullV :: MonoidalDMap k s -> Bool
  nullV m = DMap.null m

  condenseV :: forall col g. ( Foldable col, FunctorMaybe col, Functor col )
            => col (MonoidalDMap k g)
            -> MonoidalDMap k (Compose col g)
  condenseV col = condenseD' (fold (fmap unMonoidalDMap col)) col

  disperseV :: forall col g. (Align col)
           => MonoidalDMap k (Compose col g)
           -> col (MonoidalDMap k g)
  disperseV row = case findPivotD (unMonoidalDMap row) of
    NoneD -> nil
    OneD k (Compose v) -> fmap (DMap.singleton k) v
    SplitD pivot _l _r -> uncurry (alignWith (mergeThese unionDistinctAscD)) $
      disperseV *** disperseV $ splitLTD pivot row

  mapV :: (forall a. f a -> g a) -> MonoidalDMap k f -> MonoidalDMap k g
  mapV f m = DMap.map f m

  traverseV :: (Applicative m) => (forall a. f a -> m (g a)) -> MonoidalDMap k f -> m (MonoidalDMap k g)
  traverseV f m = DMap.traverseWithKey (\_ v -> f v) m

  mapMaybeV f (MonoidalDMap m) = collapseNullV $ MonoidalDMap $
    DMap'.mapMaybe f m

condenseD' :: (GCompare k, Foldable t, FunctorMaybe t)
           => DMap k g
           -> t (MonoidalDMap k g)
           -> MonoidalDMap k (Compose t g)
condenseD' folded col = case findPivotD folded of
  NoneD -> DMap.empty
  OneD k _ -> DMap.singleton k (Compose $ fmapMaybe (DMap.lookup k) col)
  SplitD pivot l r -> uncurry unionDistinctAscD $ (condenseD' l *** condenseD' r) $ splitD pivot col

unionDistinctAscD :: (GCompare k) => MonoidalDMap k g -> MonoidalDMap k g -> MonoidalDMap k g
unionDistinctAscD = DMap.unionWithKey (\_ x _ -> x)

splitD :: (GCompare k, FunctorMaybe t)
       => k x -> t (MonoidalDMap k g) -> (t (MonoidalDMap k g), t (MonoidalDMap k g))
splitD pivot col = unalignProperly $ fmapMaybe (splitOneD pivot) col

splitOneD :: (GCompare k) => k v -> MonoidalDMap k g -> Maybe (These (MonoidalDMap k g) (MonoidalDMap k g))
splitOneD pivot m =
  let (l, r) = splitLTD pivot m
  in case (DMap.null l, DMap.null r) of
    (True, True) -> Nothing
    (False, True) -> Just $ This l
    (True, False) -> Just $ That r
    (False, False) -> Just $ These l r

splitLTD :: GCompare k => k v -> MonoidalDMap k g -> (MonoidalDMap k g, MonoidalDMap k g)
splitLTD k m = case DMap.splitLookup k m of
  (l, Just v, r) -> (DMap.insert k v l, r)
  (l, Nothing, r) -> (l, r)

data PivotD (k :: l -> *) (g :: l -> *) = NoneD | forall v. OneD (k v) (g v) | forall v. SplitD (k v) (DMap k g) (DMap k g)

findPivotD :: (GCompare k) => DMap k g -> PivotD k g
findPivotD m = case m of
  Tip -> NoneD
  Bin _ k v l r
    | DMap'.null l && DMap'.null r -> OneD k v
    | otherwise -> SplitD k (DMap'.insert k v l) r

------- The View instance for Vessel itself --------

instance (Has View k, GCompare k) => View (Vessel k) where
  cropV :: (forall a. s a -> i a -> r a) -> Vessel k s -> Vessel k i -> Vessel k r
  cropV f sv iv = intersectionWithKeyV (\k s i -> has @View k (cropV f s i)) sv iv
  subtractV :: (forall a. s a -> s a -> Maybe (s a)) -> Vessel k s -> Vessel k s -> Maybe (Vessel k s)
  subtractV f sv iv = collapseNullV $ differenceWithKeyV (\k s i -> has @View k (subtractV f s i)) sv iv
  nullV :: Vessel k i -> Bool
  nullV (Vessel m) = DMap.null m
  mapV :: (forall a. f a -> g a) -> Vessel k f -> Vessel k g
  mapV f (Vessel m) = Vessel (DMap.mapWithKey (\k (FlipAp v) -> has @View k $ FlipAp (mapV f v)) m)
  traverseV :: (Applicative m) => (forall a. f a -> m (g a)) -> Vessel k f -> m (Vessel k g)
  traverseV f m = traverseWithKeyV (\k v -> has @View k $ traverseV f v) m
  condenseV :: (Foldable t, FunctorMaybe t, Functor t)
            => t (Vessel k g)
            -> Vessel k (Compose t g)
  condenseV col = condenseV' folded col
    where folded = fold $ fmap (unMonoidalDMap . unVessel) col
  disperseV :: (Align t) => Vessel k (Compose t g) -> t (Vessel k g)
  disperseV row = case findPivotD (unMonoidalDMap (unVessel row)) of
    NoneD -> nil
    OneD k (FlipAp v) -> fmap (singletonV k) (has @View k (disperseV v))
    SplitD pivot _l _r -> uncurry (alignWith (mergeThese unionDistinctAscV)) $
      disperseV *** disperseV $ splitLTV pivot row
  mapMaybeV f (Vessel (MonoidalDMap m)) = collapseNullV $ Vessel $ MonoidalDMap $
    DMap'.mapMaybeWithKey (\k (FlipAp v) -> has @View k $ FlipAp <$> mapMaybeV f v) m

condenseV' :: forall k t g.
              ( Has View k, GCompare k, Foldable t, FunctorMaybe t, Functor t)
           => DMap k (FlipAp g)
           -> t (Vessel k g)
           -> Vessel k (Compose t g)
condenseV' folded col =
  case findPivotD folded of
    NoneD -> emptyV
    OneD (k :: k v) _ -> singletonV k (has @View k (condenseV $ fmapMaybe (lookupV k) col))
    SplitD pivot l r -> uncurry unionDistinctAscV $ (condenseV' l *** condenseV' r) $ splitV pivot col

unionDistinctAscV :: (GCompare k) => Vessel k g -> Vessel k g -> Vessel k g
unionDistinctAscV (Vessel l) (Vessel r) = Vessel $ DMap.unionWithKey (\_ x _ -> x) l r

splitV :: forall k t g x. (GCompare k, FunctorMaybe t)
       => k x -> t (Vessel k g) -> (t (Vessel k g), t (Vessel k g))
splitV pivot col = unalignProperly $ fmapMaybe (splitOneV pivot) col

splitOneV :: (GCompare k) => k v -> Vessel k g -> Maybe (These (Vessel k g) (Vessel k g))
splitOneV pivot m =
  let (l@(Vessel l'), r@(Vessel r')) = splitLTV pivot m
  in case (DMap.null l', DMap.null r') of
    (True, True) -> Nothing
    (False, True) -> Just $ This l
    (True, False) -> Just $ That r
    (False, False) -> Just $ These l r

splitLTV :: GCompare k => k v -> Vessel k g -> (Vessel k g, Vessel k g)
splitLTV k (Vessel m) = case DMap.splitLookup k m of
  (l, Just v, r) -> (Vessel (DMap.insert k v l), Vessel r)
  (l, Nothing, r) -> (Vessel l, Vessel r)

mapDecomposedV
  :: (Functor m, View v)
  => (v Proxy -> m (v Identity))
  -> v (Compose (MonoidalMap c) g)
  -> m (v (Compose (MonoidalMap c) Identity))
mapDecomposedV f v = cropV recompose v <$> (f $ mapV (\_ -> Proxy) v)
  where
    recompose :: Compose (MonoidalMap c) g a -> Identity a -> Compose (MonoidalMap c) Identity a
    recompose (Compose s) i = Compose $ i <$ s

collapseNullV :: View v => v f -> Maybe (v f)
collapseNullV v = if nullV v
  then Nothing
  else Just v

------- Miscellaneous stuff to be moved elsewhere -------

-- TODO: These belong in Data.Functor.Compose -- good luck to anyone who wants to upstream them into base though.
-- Perhaps we could start a small module filled with basic coherences like this.
assocLCompose :: (Functor f) => Compose f (Compose g h) x -> Compose (Compose f g) h x
assocLCompose (Compose x) = Compose (Compose (fmap getCompose x))

assocRCompose :: (Functor f) => Compose (Compose f g) h x -> Compose f (Compose g h) x
assocRCompose (Compose (Compose x)) = Compose (fmap Compose x)

------ TODO: Orphans that need a good home -------

instance (Has' Group f g, Has' Semigroup f g, GCompare f) => Group (MonoidalDMap f g) where
  negateG (MonoidalDMap m) = MonoidalDMap (DMap'.mapWithKey (\k v -> has' @Group @g k (negateG v)) m)

instance (Has' Group f g, Has' Semigroup f g, GCompare f) => Additive (MonoidalDMap f g)

instance Group g => Group (Const g x) where
  negateG (Const a) = Const (negateG a)
  (Const a) ~~ (Const b) = Const (a ~~ b)

instance Additive g => Additive (Const g x)

instance (Ord k, Group v) => Group (MonoidalMap k v) where
  negateG m = Map.map negateG m

instance (Ord k, Additive v) => Additive (MonoidalMap k v)

instance (Semigroup (f (g a))) => Semigroup (Compose f g a) where
  (Compose x) <> (Compose y) = Compose (x <> y)

instance (Monoid (f (g a))) => Monoid (Compose f g a) where
  mempty = Compose mempty
  mappend (Compose x) (Compose y) = Compose (mappend x y)

--------------------------------------------------

-- TODO: Contribute this to the 'these' package and/or sort out its generalisation.
unalignProperly :: (FunctorMaybe f) => f (These a b) -> (f a, f b)
unalignProperly f = (fmapMaybe leftThese f, fmapMaybe rightThese f)
  where
    leftThese :: These a b -> Maybe a
    leftThese = these (\x -> Just x) (\_ -> Nothing) (\x _ -> Just x)
    rightThese :: These a b -> Maybe b
    rightThese = these (\_ -> Nothing) (\y -> Just y) (\_ y -> Just y)

-- TODO: Class for fromDistinctAscList? In condenseV and disperseV, we might be able to improve the cost relative to
-- combining many singleton maps, if we know those maps are presented to us in sorted order.
