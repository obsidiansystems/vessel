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

module Data.Vessel.Identity where

import Data.Aeson
import Data.Patch (Group(..), Additive)
import GHC.Generics
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.These

import Data.Vessel.Class
import Data.Vessel.Selectable
import Data.Vessel.ViewMorphism

-- | A functor-indexed container corresponding to Identity. (i.e. a single non-deletable item)
newtype IdentityV (a :: *) (g :: * -> *) = IdentityV { unIdentityV :: g a }
  deriving (Eq, Ord, Show, Read, Semigroup, Monoid, Group, Additive, Generic, ToJSON, FromJSON)

instance View (IdentityV a) where
  cropV f (IdentityV s) (IdentityV x) = Just $ IdentityV $ f s x
  nullV _ = False
  condenseV m = IdentityV (Compose (fmap unIdentityV m))
  disperseV (IdentityV (Compose m)) = fmap IdentityV m
  mapV f (IdentityV x) = IdentityV (f x)
  traverseV f (IdentityV x) = IdentityV <$> f x
  mapMaybeV f (IdentityV x) = IdentityV <$> f x
  alignWithMaybeV f (IdentityV x) (IdentityV y) = IdentityV <$> f (These x y)
  alignWithV f (IdentityV x) (IdentityV y) = IdentityV $ f $ These x y

instance Selectable (IdentityV a) () where
  type Selection (IdentityV a) () = a
  selector p () = IdentityV p
  selection () (IdentityV (Identity a)) = a

lookupIdentityV :: IdentityV a Identity -> a
lookupIdentityV = runIdentity . unIdentityV

type instance ViewQueryResult (IdentityV a f) = IdentityV a (ViewQueryResult f)

identityV :: (Applicative m, Applicative n, ViewQueryResult (f a) ~ ViewQueryResult f a) => ViewMorphism m n (f a) (IdentityV a f)
identityV = ViewMorphism toIdentityV fromIdentityV

toIdentityV :: (Applicative m, Applicative n, ViewQueryResult (f a) ~ ViewQueryResult f a) => ViewHalfMorphism m n (f a) (IdentityV a f)
toIdentityV = ViewHalfMorphism
  { _viewMorphism_mapQuery = pure . IdentityV
  , _viewMorphism_mapQueryResult = pure . unIdentityV
  }
fromIdentityV :: (Applicative m, Applicative n, ViewQueryResult (f a) ~ ViewQueryResult f a) => ViewHalfMorphism m n (IdentityV a f) (f a)
fromIdentityV = ViewHalfMorphism
  { _viewMorphism_mapQuery = pure . unIdentityV
  , _viewMorphism_mapQueryResult = pure . IdentityV
  }

-- | A gadget to "traverse" over an IdentityV
handleIdentityVSelector
  :: forall a f g m. Functor m
  => (forall x. x -> f x -> g x)
  -> m a
  ->    IdentityV a f
  -> m (IdentityV a g)
handleIdentityVSelector k f (IdentityV xs) = (\y -> IdentityV $ k y xs) <$> f

-- | Non-existentialized map; since the contained value is known
mapIdentityV :: (f a -> g a) -> IdentityV a f -> IdentityV a g
mapIdentityV f (IdentityV xs) = IdentityV (f xs)


