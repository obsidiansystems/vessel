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
{-# LANGUAGE GADTs #-}

module Data.Vessel where

import Data.Aeson
import Data.Align
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Constraint hiding ((***))
import Data.Constraint.Extras
import Data.Constraint.Forall
import Data.Dependent.Map.Internal (DMap (..))
import qualified Data.Dependent.Map.Monoidal as DMap
import Data.Dependent.Map.Monoidal (MonoidalDMap(..))
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Dependent.Sum
import Data.Dependent.Sum.Orphans ()
import Data.Foldable hiding (null)
import Data.Functor.Compose
import Data.Functor.Const
import Data.GADT.Compare
import Data.Maybe
import Data.Semigroup
import Data.Some hiding (This)
import Data.These
import Control.Arrow ((***))
import Prelude hiding (lookup, map, null)
import Reflex (Group(..), Additive, Query(..), FunctorMaybe(..), ffilter)
import Data.Coerce

import Data.TSum

--import qualified Data.Map.Monoidal as Map
--import Data.Map.Monoidal (MonoidalMap)

{-
data TV a where
  TV_Email :: TV (Mapf (Id Email') (First (Maybe EmailView)))
-}

--newtype Mapf k v f = Mapf (MonoidalMap k (f v))

newtype FlipAp (g :: k) (v :: k -> *) = FlipAp { unFlipAp :: v g }

newtype Vessel (f :: ((k -> *) -> *) -> *) (g :: k -> *) = Vessel { unVessel :: MonoidalDMap f (FlipAp g) }

newtype MapView k v g = MapView { unMapView :: Map k (g v) }

data MyQuery (k :: (* -> *) -> *) where
  Email :: MyQuery (MapView Int Int)

singleton :: k v -> v g -> Vessel k g
singleton k v = Vessel (DMap.singleton k (FlipAp v))

empty :: Vessel k g
empty = Vessel (DMap.empty)

null :: Vessel k g -> Bool
null (Vessel m) = DMap.null m

lookup :: (GCompare k) => k v -> Vessel k g -> Maybe (v g)
lookup k (Vessel m) = unFlipAp <$> DMap.lookup k m

mapMaybeWithKeyVessel :: (GCompare k) => (forall v. k v -> v g -> Maybe (v g')) -> Vessel k g -> Vessel k g'
mapMaybeWithKeyVessel f (Vessel m) = Vessel (DMap.mapMaybeWithKey (\k (FlipAp x) -> FlipAp <$> f k x) m) 

--class c (t g) => ApClass (c :: k' -> Constraint) (g :: k) (t :: k -> k') where

{-
instance (ForallF Semigroup f, Semigroup (g x)) => Semigroup (Compose f g x) where

instance (ForallF Monoid f, Semigroup (g x)) => Monoid (Compose f g x) where
-}

instance Semigroup (v g) => Semigroup (FlipAp g v) where
  FlipAp x <> FlipAp y = FlipAp (x <> y)

instance (Has' Semigroup f (FlipAp g), GCompare f) => Semigroup (Vessel f g) where
  Vessel m <> Vessel n = Vessel (m <> n)

instance (Has' Semigroup f (FlipAp g), GCompare f) => Monoid (Vessel f g) where
  mempty = Vessel (DMap.empty)
  mappend = (<>)

-- disperseQ f m = Map.unionsWith (<>) . map (\(k :=> v) -> fmap (DMap.singleton k) (f v)) . DMap.toList

class Disperse row where
  disperse :: (Foldable col, FunctorMaybe col, Unalign col) => col (row a) -> row (col a)
  condense :: (Align col) => row (col a) -> col (row a)

data Pivot k a = None | One k a | Split k (Map k a) (Map k a)
  deriving (Eq, Ord, Show)

unionV :: (GCompare k) => Vessel k g -> Vessel k g -> Vessel k g
unionV (Vessel m) (Vessel m') = Vessel (DMap.unionWithKey (\_ x _ -> x) m m')

instance (Ord k) => Unalign (Map k)
instance (Ord k) => FunctorMaybe (Map k) where
  fmapMaybe = Map.mapMaybe

instance Ord k => Disperse (Map k) where
  disperse :: forall col a. (Foldable col, FunctorMaybe col, Unalign col)
           => col (Map k a)
           -> Map k (col a)
  disperse col = disperse' (fold col) col
    where
      disperse' :: Map k a
                -> col (Map k a)
                -> Map k (col a)
      disperse' folded col = case findPivot folded of
            None -> mempty
            One k _ -> Map.singleton k (fmapMaybe (Map.lookup k) col)
            Split pivot l r -> uncurry unionDistinctAsc $ (disperse' l *** disperse' r) $ split pivot col

      split :: (Ord k, FunctorMaybe col, Unalign col) => k -> col (Map k a) -> (col (Map k a), col (Map k a))
      split pivot col = fmapMaybe id *** fmapMaybe id $ unalign $ fmapMaybe (splitOne pivot) col

      splitOne :: (Ord k) => k -> Map k a -> Maybe (These (Map k a) (Map k a))
      splitOne pivot m =
        let (l, r) = splitLT pivot m
        in case (Map.null l, Map.null r) of
          (True, True) -> Nothing
          (False, True) -> Just $ This l
          (True, False) -> Just $ That r
          (False, False) -> Just $ These l r
      
  condense :: forall col a. (Align col)
           => Map k (col a)
           -> col (Map k a)
  condense row = case findPivot row of
    None -> nil
    One k v -> fmap (Map.singleton k) v
    Split pivot l r -> uncurry (alignWith (mergeThese unionDistinctAsc)) $ condense *** condense $ splitLT pivot row

findPivot :: Ord k => Map k a -> Pivot k a
findPivot m = case Map.splitRoot m of
  [] -> None
  [l,xm,r] -> case Map.toList xm of
      [(k,v)] | Map.null l && Map.null r -> One k v
              | otherwise -> Split k (Map.insert k v l) r
      _ -> errorMsg
  _ -> errorMsg
  where errorMsg = error "Data.Vessel.findPivot: unexpected result from Data.Map.splitRoot (wrong version of containers?)"

splitLT :: Ord k => k -> Map k a -> (Map k a, Map k a)
splitLT k m = case Map.splitLookup k m of
  (l, Just v, r) -> (Map.insert k v l, r)
  (l, Nothing, r) -> (l, r)

unionDistinctAsc :: (Ord k) => Map k a -> Map k a -> Map k a
unionDistinctAsc = Map.union

class (ForallF Monoid v) => View v where
  disperseV :: (Foldable t, FunctorMaybe t, Unalign t, Monoid (v g), Monoid (v (Compose t g))) => t (v g) -> v (Compose t g) 
  condenseV :: (Align t) => v (Compose t g) -> t (v g)
  mapV :: (forall a. f a -> g a) -> v f -> v g
  traverseV :: (Applicative m) => (forall a. f a -> m (g a)) -> v f -> m (v g)

instance (GCompare k, ForallF Monoid (MonoidalDMap k)) => View (MonoidalDMap k) where
  disperseV :: ( Foldable col, FunctorMaybe col, Unalign col
               , Monoid (MonoidalDMap k g)
               , Monoid (MonoidalDMap k (Compose col g)))
            => col (MonoidalDMap k g)
            -> MonoidalDMap k (Compose col g)
  disperseV col = disperseD' (fold col) col
  condenseV :: forall col g. (Align col)
           => MonoidalDMap k (Compose col g)
           -> col (MonoidalDMap k g)
  condenseV row = case findPivotD row of
    NoneD -> nil
    OneD k (Compose v) -> fmap (DMap.singleton k) v
    SplitD pivot l r -> uncurry (alignWith (mergeThese unionDistinctAscD)) $ condenseV *** condenseV $ splitLTD pivot row
  mapV :: (forall a. f a -> g a) -> MonoidalDMap k f -> MonoidalDMap k g
  mapV f m = DMap.map f m
  traverseV :: (Applicative m) => (forall a. f a -> m (g a)) -> MonoidalDMap k f -> m (MonoidalDMap k g)
  traverseV f m = DMap.traverseWithKey (\k v -> f v) m

disperseD' :: (GCompare k, Foldable t, FunctorMaybe t, Unalign t, Monoid (MonoidalDMap k (Compose t g)))
           => MonoidalDMap k g
           -> t (MonoidalDMap k g)
           -> MonoidalDMap k (Compose t g)
disperseD' folded col = case findPivotD folded of
  NoneD -> mempty
  OneD k _ -> DMap.singleton k (Compose $ fmapMaybe (DMap.lookup k) col)
  SplitD pivot l r -> uncurry unionDistinctAscD $ (disperseD' l *** disperseD' r) $ splitD pivot col

data PivotD (k :: l -> *) (g :: l -> *) = NoneD | forall v. OneD (k v) (g v) | forall v. SplitD (k v) (MonoidalDMap k g) (MonoidalDMap k g)

unionDistinctAscD :: (GCompare k) => MonoidalDMap k g -> MonoidalDMap k g -> MonoidalDMap k g
unionDistinctAscD = DMap.unionWithKey (\_ x _ -> x)

findPivotD :: (GCompare k) => MonoidalDMap k g -> PivotD k g
findPivotD (MonoidalDMap m) = case m of
  Tip -> NoneD
  Bin _ k v l r
    | DMap.null (MonoidalDMap l) && DMap.null (MonoidalDMap r) -> OneD k v
    | otherwise -> SplitD k (DMap.insert k v (MonoidalDMap l)) (MonoidalDMap r)

splitD :: (GCompare k, FunctorMaybe t, Unalign t)
       => k x -> t (MonoidalDMap k g) -> (t (MonoidalDMap k g), t (MonoidalDMap k g))
splitD pivot col = fmapMaybe id *** fmapMaybe id $ unalign $ fmapMaybe (splitOneD pivot) col

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

instance (Has View k, GCompare k, ForallF Monoid (Vessel k)) => View (Vessel k) where
  mapV :: (forall a. f a -> g a) -> Vessel k f -> Vessel k g
  mapV f (Vessel m) = Vessel (DMap.mapWithKey (\k (FlipAp v) -> has @View k $ FlipAp (mapV f v)) m)
  traverseV :: (Applicative m) => (forall a. f a -> m (g a)) -> Vessel k f -> m (Vessel k g)
  traverseV f (Vessel m) = fmap Vessel (DMap.traverseWithKey (\k (FlipAp v) -> has @View k $ fmap FlipAp (traverseV f v)) m)
  disperseV :: (Foldable t, FunctorMaybe t, Unalign t, Monoid (Vessel k g), Monoid (Vessel k (Compose t g)))
            => t (Vessel k g)
            -> Vessel k (Compose t g)
  disperseV col = disperseV' (fold col) col
  condenseV :: (Align t) => Vessel k (Compose t g) -> t (Vessel k g)
  condenseV row = case findPivotV row of
    NoneV -> nil
    OneV k v -> fmap (singleton k) (has @View k (condenseV v))
    SplitV pivot l r -> uncurry (alignWith (mergeThese unionDistinctAscV)) $ condenseV *** condenseV $ splitLTV pivot row

disperseV' :: forall k t g.
              ( Has View k, GCompare k, Foldable t, FunctorMaybe t
              , Unalign t, Monoid (Vessel k g), Monoid (Vessel k (Compose t g)))
           => Vessel k g
           -> t (Vessel k g)
           -> Vessel k (Compose t g)
disperseV' folded col =
  case findPivotV folded of
    NoneV -> empty
    OneV (k :: k v) _ -> singleton k (has @View k (whichever @Monoid @v @g (whichever @Monoid @v @(Compose t g) (disperseV $ fmapMaybe (lookup k) col))))
    SplitV pivot l r -> uncurry unionDistinctAscV $ (disperseV' l *** disperseV' r) $ splitV pivot col

data PivotV (k :: ((l -> *) -> *) -> *) (g :: l -> *) = NoneV | forall v. OneV (k v) (v g) | forall v. SplitV (k v) (Vessel k g) (Vessel k g)

findPivotV :: (GCompare k) => Vessel k g -> PivotV k g
findPivotV (Vessel m) = case findPivotD m of
  NoneD -> NoneV
  OneD k (FlipAp v) -> OneV k v
  SplitD k l r -> SplitV k (Vessel l) (Vessel r)

unionDistinctAscV :: (GCompare k) => Vessel k g -> Vessel k g -> Vessel k g
unionDistinctAscV (Vessel l) (Vessel r) = Vessel $ DMap.unionWithKey (\_ x _ -> x) l r

splitV :: forall k t g x. (GCompare k, FunctorMaybe t, Unalign t)
       => k x -> t (Vessel k g) -> (t (Vessel k g), t (Vessel k g))
splitV pivot col = fmapMaybe id *** fmapMaybe id $ unalign $ fmapMaybe (splitOneV pivot) col

splitOneV :: (GCompare k) => k v -> Vessel k g -> Maybe (These (Vessel k g) (Vessel k g))
splitOneV pivot m =
  let (l, r) = splitLTV pivot m
  in case (null l, null r) of
    (True, True) -> Nothing
    (False, True) -> Just $ This l
    (True, False) -> Just $ That r
    (False, False) -> Just $ These l r

splitLTV :: GCompare k => k v -> Vessel k g -> (Vessel k g, Vessel k g)
splitLTV k (Vessel m) = case DMap.splitLookup k m of
  (l, Just v, r) -> (Vessel (DMap.insert k v l), Vessel r)
  (l, Nothing, r) -> (Vessel l, Vessel r)

-- TODO: Class for fromDistinctAscList? In disperseV and condenseV, we might be able to improve the cost relative to
-- combining many singleton maps, if we know those maps are presented to us in sorted order.
{-
foldMapQ :: (Monoid m) => (forall a. f a -> m) -> v f -> m
fmapMaybeQ :: (forall a. f a -> Maybe (g a)) -> v f -> v g
alignWithQ :: (forall a. These (f a) (g a) -> h a) -> (v f, v g) -> v h
unalignWithQ :: (forall a. f a -> These (g a) (h a)) -> v f -> (v g, v h)
-}