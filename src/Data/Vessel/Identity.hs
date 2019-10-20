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

module Data.Vessel.Identity where

import Data.Aeson
import Reflex.Patch (Group(..), Additive)
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
  deriving (Eq, Ord, Show, Read, Semigroup, Monoid, Group, Additive, Generic)

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

instance ToJSON (g a) => ToJSON (IdentityV a g)

instance FromJSON (g a) => FromJSON (IdentityV a g)

instance Selectable (IdentityV a) () where
  type Selection (IdentityV a) () = a
  selector p () = IdentityV p
  selection () (IdentityV (Identity a)) = a

lookupIdentityV :: IdentityV a Identity -> a
lookupIdentityV = runIdentity . unIdentityV

type instance ViewQueryResult (IdentityV a (Const g)) = IdentityV a Identity

identityV :: ViewMorphism (Const g a) (IdentityV a (Const g))
identityV = ViewMorphism
  { _viewMorphism_mapQuery = IdentityV
  , _viewMorphism_mapQueryResult = Just . unIdentityV
  }

