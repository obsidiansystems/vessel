{-# LANGUAGE PolyKinds #-}

module Data.Vessel
  ( Vessel(..)
  , View(..)
  , EmptyView(..)
  , Selectable(..)
  , FlipAp(..)
  , IdentityV(..)
  , SingleV(..)
  , MapV(..)
  , DMapV(..)
  , singletonV
  , lookupV
  , buildV
  , subtractV
  , mapMaybeWithKeyV
  , traverseWithKeyV
  , traverseWithKeyV_
  , intersectionWithKeyV
  , mapDecomposedV
  , alignWithMV
  , collapseNullV
  , VSum (..)
  , toListV
  , fromListV
  , module Data.Proxy
  , module Data.Functor.Identity
  , module Data.Functor.Const
  , module Data.Functor.Compose
  , transposeView
  , Disperse(..)
  , SubVessel(..)
  , traverseSubVessel
  , singletonSubVessel
  , lookupSubVessel
  ) where

import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.Proxy

import Data.Vessel.Class as X
import Data.Vessel.Disperse as X
import Data.Vessel.Selectable as X
import Data.Vessel.Vessel as X
import Data.Vessel.DependentMap as X
import Data.Vessel.Identity as X
import Data.Vessel.Internal as X
import Data.Vessel.Map as X
import Data.Vessel.Single as X
import Data.Vessel.SubVessel as X
import Data.Vessel.ViewMorphism as X
