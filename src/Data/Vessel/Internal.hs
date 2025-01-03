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

{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Vessel.Internal where

import Control.Arrow ((***))
import Data.Aeson
import Data.Coerce
import Data.Constraint.Extras
import Data.Constraint.Forall
import qualified Data.Dependent.Map as DMap'
import Data.Dependent.Map.Internal (DMap(..))
import Data.Dependent.Map.Monoidal (MonoidalDMap(..))
import Data.Functor.Compose
import Data.Functor.Const
import Data.GADT.Compare
import Data.Kind (Type)
import qualified Data.Map as Map'
import qualified Data.Map.Merge.Strict as Map'
import Data.Map.Monoidal (MonoidalMap(..))
import qualified Data.Map.Monoidal as Map
import Data.Patch (Group(..))
import Data.Semigroup.Commutative
import Data.Set (Set)
import Data.Some (Some(Some))
import Data.These
import GHC.Generics
import Witherable

import qualified Data.Dependent.Map.Monoidal as DMap
-- import qualified Data.Dependent.Map as DMap'

newtype FlipAp (g :: k) (v :: k -> Type) = FlipAp { unFlipAp :: v g }
  deriving (Eq, Ord, Show)

------- Instances for FlipAp -------

instance Semigroup (v g) => Semigroup (FlipAp g v) where
  FlipAp x <> FlipAp y = FlipAp (x <> y)

instance Monoid (v g) => Monoid (FlipAp g v) where
  mempty = FlipAp mempty

instance Group (v g) => Group (FlipAp g v) where
  negateG (FlipAp x) = FlipAp (negateG x)

instance Commutative (v g) => Commutative (FlipAp g v)


-- A single Vessel key/value pair, essentially a choice of container type, together with a corresponding container.
data VSum (k :: ((x -> Type) -> Type) -> Type) (g :: x -> Type) = forall v. k v :~> v g

------- Serialisation -------

instance (ForallF ToJSON k, HasV ToJSON k g) => ToJSON (VSum k g) where
  toJSON ((k :: k v) :~> (v :: v g)) =
    toJSON ( whichever @ToJSON @k @v (toJSON k)
           , hasV @ToJSON @g k (toJSON v))

instance forall k g. (FromJSON (Some k), HasV FromJSON k g) => FromJSON (VSum k g) where
  parseJSON x = do
    (jk, jv) <- parseJSON x
    (Some k) <- parseJSON jk
    v <- hasV @FromJSON @g k (parseJSON jv)
    return (k :~> v)
--
------ TODO: Orphans that need a good home -------

instance (Has' Group f g, Has' Semigroup f g, GCompare f) => Group (MonoidalDMap f g) where
  negateG (MonoidalDMap m) = MonoidalDMap (DMap'.mapWithKey (\k v -> has' @Group @g k (negateG v)) m)

instance (Has' Group f g, Has' Semigroup f g, GCompare f) => Commutative (MonoidalDMap f g)

instance (Commutative (f (g a))) => Commutative (Compose f g a)

------- Miscellaneous stuff to be moved elsewhere -------

-- TODO: These belong in Data.Functor.Compose -- good luck to anyone who wants to upstream them into base though.
-- Perhaps we could start a small module filled with basic coherences like this.
assocLCompose :: (Functor f) => Compose f (Compose g h) x -> Compose (Compose f g) h x
assocLCompose (Compose x) = Compose (Compose (fmap getCompose x))

assocRCompose :: (Functor f) => Compose (Compose f g) h x -> Compose f (Compose g h) x
assocRCompose (Compose (Compose x)) = Compose (fmap Compose x)

assocLComposeComp :: (Functor f) => (Compose f (g :.: h)) x -> ((Compose f g) :.: h) x
assocLComposeComp (Compose x) = Comp1 $ Compose (fmap unComp1 x)

assocRComposeComp :: (Functor f) => ((Compose f g) :.: h) x -> Compose f (g :.: h) x
assocRComposeComp (Comp1 (Compose x)) = Compose (fmap Comp1 x)

alignWithKeyMaybeDMap :: GCompare k => (forall a. k a -> These (f a) (g a) -> Maybe (h a)) -> DMap k f -> DMap k g -> DMap k h
alignWithKeyMaybeDMap f a b = DMap'.mapMaybeWithKey (\k t -> f k $ dtheseToThese t) $ DMap'.unionWithKey (\_ (DThis x) (DThat y) -> DThese x y) (DMap'.map DThis a) (DMap'.map DThat b)

alignWithKeyDMap :: GCompare k => (forall a. k a -> These (f a) (g a) -> h a) -> DMap k f -> DMap k g -> DMap k h
alignWithKeyDMap f a b = DMap'.mapWithKey (\k t -> f k $ dtheseToThese t) $ DMap'.unionWithKey (\_ (DThis x) (DThat y) -> DThese x y) (DMap'.map DThis a) (DMap'.map DThat b)

data DThese f g a = DThis (f a) | DThat (g a) | DThese (f a) (g a)

dtheseToThese :: DThese f g a -> These (f a) (g a)
dtheseToThese = \case
  DThis a -> This a
  DThat b -> That b
  DThese a b -> These a b

theseToDThese :: These (f a) (g a) -> DThese f g a
theseToDThese = \case
  This a -> DThis a
  That b -> DThat b
  These a b -> DThese a b

-- TODO: Contribute this to the 'these' package and/or sort out its generalisation.
unalignProperly :: (Filterable f) => f (These a b) -> (f a, f b)
unalignProperly f = (mapMaybe leftThese f, mapMaybe rightThese f)
  where
    leftThese :: These a b -> Maybe a
    leftThese = these (\x -> Just x) (\_ -> Nothing) (\x _ -> Just x)
    rightThese :: These a b -> Maybe b
    rightThese = these (\_ -> Nothing) (\y -> Just y) (\_ y -> Just y)

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

unionDistinctAsc :: (Ord k) => MonoidalMap k a -> MonoidalMap k a -> MonoidalMap k a
unionDistinctAsc = Map.unionWith (\x _ -> x)

splitLT :: Ord k => k -> MonoidalMap k a -> (MonoidalMap k a, MonoidalMap k a)
splitLT k m = case Map.splitLookup k m of
  (l, Just v, r) -> (Map.insert k v l, r)
  (l, Nothing, r) -> (l, r)

data PivotD (k :: l -> Type) (g :: l -> Type) = NoneD | forall v. OneD (k v) (g v) | forall v. SplitD (k v) (DMap k g) (DMap k g)

condenseD' :: (GCompare k, Foldable t, Filterable t)
           => DMap k g
           -> t (MonoidalDMap k g)
           -> MonoidalDMap k (Compose t g)
condenseD' folded col = case findPivotD folded of
  NoneD -> DMap.empty
  OneD k _ -> DMap.singleton k (Compose $ mapMaybe (DMap.lookup k) col)
  SplitD pivot l r -> uncurry unionDistinctAscD $ (condenseD' l *** condenseD' r) $ splitD pivot col

findPivotD :: (GCompare k) => DMap k g -> PivotD k g
findPivotD m = case m of
  Tip -> NoneD
  Bin _ k v l r
    | DMap'.null l && DMap'.null r -> OneD k v
    | otherwise -> SplitD k (DMap'.insert k v l) r

unionDistinctAscD :: (GCompare k) => MonoidalDMap k g -> MonoidalDMap k g -> MonoidalDMap k g
unionDistinctAscD = DMap.unionWithKey (\_ x _ -> x)

splitLTD :: GCompare k => k v -> MonoidalDMap k g -> (MonoidalDMap k g, MonoidalDMap k g)
splitLTD k m = case DMap.splitLookup k m of
  (l, Just v, r) -> (DMap.insert k v l, r)
  (l, Nothing, r) -> (l, r)

alignWithKeyMonoidalDMap :: GCompare k => (forall a. k a -> These (f a) (g a) -> h a) -> MonoidalDMap k f -> MonoidalDMap k g -> MonoidalDMap k h
alignWithKeyMonoidalDMap f (MonoidalDMap a) (MonoidalDMap b) = MonoidalDMap $ alignWithKeyDMap f a b


alignWithKeyMaybeMonoidalDMap :: GCompare k => (forall a. k a -> These (f a) (g a) -> Maybe (h a)) -> MonoidalDMap k f -> MonoidalDMap k g -> MonoidalDMap k h
alignWithKeyMaybeMonoidalDMap f (MonoidalDMap a) (MonoidalDMap b) = MonoidalDMap $ alignWithKeyMaybeDMap f a b

splitD :: (GCompare k, Filterable t)
       => k x -> t (MonoidalDMap k g) -> (t (MonoidalDMap k g), t (MonoidalDMap k g))
splitD pivot col = unalignProperly $ mapMaybe (splitOneD pivot) col

splitOneD :: (GCompare k) => k v -> MonoidalDMap k g -> Maybe (These (MonoidalDMap k g) (MonoidalDMap k g))
splitOneD pivot m =
  let (l, r) = splitLTD pivot m
  in case (DMap.null l, DMap.null r) of
    (True, True) -> Nothing
    (False, True) -> Just $ This l
    (True, False) -> Just $ That r
    (False, False) -> Just $ These l r

instance Group (f (g x)) => Group (Compose f g x) where
  negateG (Compose fgx) = Compose (negateG fgx)
  Compose fgx ~~ Compose fgy = Compose (fgx ~~ fgy)

curryMMap :: (Ord a, Ord b) => MonoidalMap (a,b) c -> MonoidalMap a (MonoidalMap b c)
curryMMap m = Map.fromListWith (Map.unionWith (error "overlap")) $
  [ (a, (Map.singleton b c))
  | ((a,b), c) <- Map.toList m
  ]

uncurryMMap :: (Ord a, Ord b) => MonoidalMap a (MonoidalMap b c) -> MonoidalMap (a,b) c
uncurryMMap m = Map.fromListWith (error "overlap") $
  [ ((a, b), c)
  | (a, bc) <- Map.toList m
  , (b, c) <- Map.toList bc
  ]

leftOuterJoin :: Ord k => (a -> c) -> (a -> b -> c) -> MonoidalMap k a -> MonoidalMap k b -> MonoidalMap k c
leftOuterJoin =
  (coerce :: ((a -> c) -> (a -> b -> c) -> Map'.Map k a -> Map'.Map k b -> Map'.Map k c)
          -> ((a -> c) -> (a -> b -> c) -> MonoidalMap k a -> MonoidalMap k b -> MonoidalMap k c)
  ) leftOuterJoin'

leftOuterJoin' :: Ord k => (a -> c) -> (a -> b -> c) -> Map'.Map k a -> Map'.Map k b -> Map'.Map k c
leftOuterJoin' a2c ab2c = Map'.merge
    (Map'.mapMissing $ \_ -> a2c)
    Map'.dropMissing
    (Map'.zipWithMatched $ \_ -> ab2c)

leftOuterJoin_ :: Ord k => a -> Set k -> MonoidalMap k a -> MonoidalMap k a
leftOuterJoin_ x = leftOuterJoin id const . Map.fromSet (const x)
