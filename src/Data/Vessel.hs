{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Vessel where

import Data.Aeson
import Data.Align
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Constraint
import Data.Constraint.Extras
import Data.Constraint.Forall
import Data.Dependent.Map.Monoidal
import Data.Dependent.Sum.Orphans ()
import Data.Functor.Compose
import Data.Functor.Const
import Data.GADT.Compare
import Data.Maybe
import Data.Semigroup
import Data.Some hiding (This)
import Data.These
import Prelude hiding (lookup, map)
import Reflex (Group(..), Additive, Query(..), FunctorMaybe(..))

newtype Vessel f g a = Vessel { unVessel :: MonoidalDMap f (g a) }
  deriving (Eq, Ord, Read, Show)

deriving instance (ForallF ToJSON f, Has ToJSON f, ToJSON1 (g a)) => ToJSON (Vessel f g a)
deriving instance (FromJSON (Some f), GCompare f, Has FromJSON f, FromJSON1 (g a)) => FromJSON (Vessel f g a)

instance (Bifunctor g) => Functor (Vessel f g) where
  fmap f (Vessel m) = Vessel (map (first f) m)

instance (Bifoldable g) => Foldable (Vessel f g) where
  foldr f i (Vessel m) = foldrWithKey (\_ v x -> bifoldr f (const id) x v) i m

instance (Bitraversable g) => Traversable (Vessel f g) where
  traverse f (Vessel m) = fmap Vessel (traverseWithKey (\_ v -> bitraverse f pure v) m)

instance (GCompare f, Has Semigroup f, Biapplicative g) => Align (Vessel f g) where
  nil = Vessel empty
  align m n = Vessel (unionWithKey combine m' n')
    where
      Vessel m' = fmap This m
      Vessel n' = fmap That n
      combine :: forall a b c. f c -> g (These a b) c -> g (These a b) c -> g (These a b) c
      combine f x y
        | Dict <- argDict f :: Dict (Semigroup c) = bipure (\(This u) (That v) -> These u v) (<>) <<*>> x <<*>> y

instance (GCompare f, Biapplicative g, Semigroup a, Has Semigroup f) => Semigroup (Vessel f g a) where
  m <> n = salign m n

instance (GCompare f, Biapplicative g, Semigroup a, Has Semigroup f) => Monoid (Vessel f g a) where
  mempty = Vessel empty
  mappend = (<>)

instance (GCompare f, Biapplicative g, Has Semigroup f, Bifunctor g, Group a) => Group (Vessel f g a) where
  negateG = fmap negateG

instance (GCompare f, Biapplicative g, Has Semigroup f, Bifunctor g, Group a, Additive a) => Additive (Vessel f g a)

instance (GCompare f, Has Semigroup f, Semigroup a) => Query (Vessel f Const a) where
  type QueryResult (Vessel f Const a) = Vessel f (,) a
  crop (Vessel q) (Vessel v) = Vessel (intersectionWithKey (\_ _ x -> x) q v)

instance (GCompare f, Bitraversable g) => FunctorMaybe (Vessel f g) where
  fmapMaybe f (Vessel v) = Vessel (mapMaybeWithKey (\_ x -> bitraverse f Just x) v)

singletonVS :: (Num n) => k t -> Vessel k Const n
singletonVS q = Vessel (singleton q (Const 1))

singletonV :: k t -> t -> a -> Vessel k (,) a
singletonV q v a = Vessel (singleton q (a, v))

lookupV :: (GCompare k) => k t -> Vessel k (,) a -> Maybe t
lookupV q (Vessel m) = fmap snd (lookup q m)

lookupV' :: (GCompare k) => k (First (Maybe t)) -> Vessel k (,) a -> Maybe t
lookupV' q (Vessel m) = do
  x <- fmap snd (lookup q m)
  getFirst x

-- Given a view selector and a body which determines the response for each key, produces a view.
buildV :: forall m k a. (Monad m, GCompare k) => Vessel k Const a -> (forall x. k x -> m (Maybe x)) -> m (Vessel k (,) a)
buildV (Vessel q) f = fmap (Vessel . mapMaybeWithKey (\_ (Compose m) -> m)) $ traverseWithKey body q 
  where
    body :: k x -> Const a x -> m (Compose Maybe ((,) a) x)
    body k (Const a) = do
      mr <- f k
      return (Compose (fmap ((,) a) mr))
