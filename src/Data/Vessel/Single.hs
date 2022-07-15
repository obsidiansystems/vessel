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
import Data.Patch (Group(..), Additive)
import Data.Semigroup
import Data.Functor.Identity
import Data.Witherable
import Data.Functor.Compose
import Data.Functor.Const
import Data.Align
import Data.Aeson
import GHC.Generics (Generic)

import Data.Vessel.Class
import Data.Vessel.Selectable
import Data.Vessel.ViewMorphism

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

lookupSingleV :: SingleV a Identity -> Maybe a
lookupSingleV = getFirst . runIdentity . unSingleV

type instance ViewQueryResult (SingleV a f) = SingleV a (ViewQueryResult f)

-- Note.  the result functions always return Just;  a "Single" is always
-- present in the result, only that the value it may be is possibly a Nothing.
singleV :: (Applicative m, Applicative n, Functor f, Functor (ViewQueryResult f), ViewQueryResult f (Maybe a) ~ ViewQueryResult (f (Maybe a))) => ViewMorphism m n (f (Maybe a)) (SingleV a f)
singleV = ViewMorphism toSingleV fromSingleV

toSingleV :: (Functor f, Functor (ViewQueryResult f), Applicative m, Applicative n, ViewQueryResult f (Maybe a) ~ ViewQueryResult (f (Maybe a))) => ViewHalfMorphism m n (f (Maybe a)) (SingleV a f)
toSingleV = ViewHalfMorphism
  { _viewMorphism_mapQuery = \xs -> pure . SingleV $ fmap First xs
  , _viewMorphism_mapQueryResult = \(SingleV xs) -> pure $ fmap getFirst xs
  }

fromSingleV :: (Functor f, Functor (ViewQueryResult f), Applicative m, Applicative n, ViewQueryResult f (Maybe a) ~ ViewQueryResult (f (Maybe a))) => ViewHalfMorphism m n (SingleV a f) (f (Maybe a))
fromSingleV = ViewHalfMorphism
  { _viewMorphism_mapQuery = \(SingleV xs) -> pure $ fmap getFirst xs
  , _viewMorphism_mapQueryResult = pure . SingleV . fmap First
  }
-- | A gadget to "traverse" over a SingleV
handleSingleVSelector
  :: forall a f g m. Functor m
  => (forall x. x -> f x -> g x)
  -> m (First (Maybe a))
  ->    SingleV a f
  -> m (SingleV a g)
handleSingleVSelector k f (SingleV xs) = (\y -> SingleV $ k y xs) <$> f

-- | Non-existentialized mapV; since the contained value is known
mapSingleV :: (f (First (Maybe a)) -> g (First (Maybe a))) -> SingleV a f -> SingleV a g
mapSingleV f (SingleV xs) = SingleV (f xs)
