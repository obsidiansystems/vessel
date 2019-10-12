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

module Data.Vessel.Single where

import Data.These
import Reflex.Patch (Group(..), Additive)
import Data.Semigroup
import Data.Functor.Identity
import Data.Witherable
import Data.Functor.Compose
import Data.Align
import Data.Aeson
import GHC.Generics (Generic)

import Data.Vessel.Class
import Data.Vessel.Selectable

------- Simple structure components -------

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
  cropV f (SingleV s) (SingleV i) = Just $ SingleV $ f s i
  nullV (SingleV _) = False
  condenseV :: (Foldable t, Filterable t, Functor t) => t (SingleV a g) -> SingleV a (Compose t g)
  condenseV m = SingleV . Compose $ fmap unSingleV m
  disperseV :: (Align t) => SingleV a (Compose t g) -> t (SingleV a g)
  disperseV (SingleV (Compose x)) = fmap SingleV x
  mapV :: (forall x. f x -> g x) -> SingleV a f -> SingleV a g
  mapV f (SingleV x) = SingleV $ f x
  traverseV :: (Applicative m) => (forall x. f x -> m (g x)) -> SingleV a f -> m (SingleV a g)
  traverseV f (SingleV x) = SingleV <$> f x
  mapMaybeV f (SingleV x) = SingleV <$> f x
  alignWithMaybeV f (SingleV x) (SingleV y) = SingleV <$> f (These x y)
  alignWithV f (SingleV x) (SingleV y) = SingleV $ f $ These x y

deriving instance ToJSON (g (First (Maybe a))) => ToJSON (SingleV a g)

deriving instance FromJSON (g (First (Maybe a))) => FromJSON (SingleV a g)

instance Selectable (SingleV a) () where
  type Selection (SingleV a) () = Maybe a
  selector p () = SingleV p
  selection () (SingleV x) = getFirst . runIdentity $ x

