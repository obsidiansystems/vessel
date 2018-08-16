{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module Data.TSum where

import Control.Applicative
import Data.GADT.Compare
import Data.GADT.Show
import Data.Aeson
import Data.Aeson.Types (typeMismatch)
import GHC.Generics
import Data.Typeable
import Data.Some
import Data.Dependent.Sum
import Data.Constraint.Extras

data TSum t f g a = Public (f a) | Private t (g a)
  deriving (Eq, Ord, Show, Read, Generic, Typeable)

instance (ArgDict f, ArgDict g) => ArgDict (TSum t f g) where
  type ConstraintsFor c (TSum t f g) = (ConstraintsFor c f, ConstraintsFor c g)
  argDict (Public x) = argDict x
  argDict (Private _ x) = argDict x

instance (GEq f, GEq g) => GEq (TSum t f g) where
  geq (Public x) (Public y) = geq x y
  geq (Private _ x) (Private _ y) = geq x y
  geq _ _ = Nothing

instance (Ord t, GCompare f, GCompare g) => GCompare (TSum t f g) where
  gcompare (Public _) (Private _ _) = GLT
  gcompare (Private _ _) (Public _) = GGT
  gcompare (Public x) (Public y) = gcompare x y
  gcompare (Private t x) (Private t' y) =
    case compare t t' of
      LT -> GLT
      GT -> GGT
      EQ -> gcompare x y

instance (Show t, GShow f, GShow g) => GShow (TSum t f g) where
  gshowsPrec d (Public x) = showParen (d > 10)
    (showString "Public " . gshowsPrec 11 x)
  gshowsPrec d (Private t x) = showParen (d > 10)
    (showString "Private " . showsPrec 11 t . showString " " . gshowsPrec 11 x)

instance (ToJSON t, ToJSON (f a), ToJSON (g a)) => ToJSON (TSum t f g a) where
  toJSON (Public x) = object ["tag" .= String "Public", "contents" .= toJSON x]
  toJSON (Private t x) = object ["tag" .= String "Private", "contents" .= toJSON x, "token" .= toJSON t]

instance (FromJSON t, FromJSON (Some f), FromJSON (Some g)) => FromJSON (Some (TSum t f g)) where
  parseJSON v = do
    o <- parseJSON v
    let publicParser = do
          String "Public" <- o .: "tag"
          This x <- o .: "contents"
          return (This (Public x))
        privateParser = do
          String "Private" <- o .: "tag"
          This x <- o .: "contents"
          t <- o .: "token"
          return (This (Private t x))
    publicParser <|> privateParser <|> typeMismatch "TSum" v

instance (EqTag f h, EqTag g h) => EqTag (TSum t f g) h where
  eqTagged (Public x) (Public y) = eqTagged x y
  eqTagged (Private _ x) (Private _ y) = eqTagged x y
  eqTagged _ _ = error "eqTagged for TSum applied to unequal tags"

instance (Ord t, OrdTag f h, OrdTag g h) => OrdTag (TSum t f g) h where
  compareTagged (Public x) (Public y) = compareTagged x y
  compareTagged (Private _ x) (Private _ y) = compareTagged x y
  compareTagged _ _ = error "compareTagged for TSum applied to unequal tags"

instance (Show t, ShowTag f h, ShowTag g h) => ShowTag (TSum t f g) h where
  showTaggedPrec (Public x) = showTaggedPrec x
  showTaggedPrec (Private _ x) = showTaggedPrec x

data Empty a

deriving instance Eq (Empty a)
deriving instance Ord (Empty a)
deriving instance Show (Empty a)

instance GEq Empty where
  geq _ _ = Nothing

instance GCompare Empty where
  gcompare _ _ = error "gcompare applied for Empty" -- Shouldn't happen

instance EqTag Empty h where
  eqTagged _ _ _ _ = False

instance OrdTag Empty h where
  compareTagged _ _ _ _ = error "compareTagged applied for Empty" -- Shouldn't happen

instance GShow Empty where
  gshowsPrec = showsPrec

instance ToJSON (Empty a) where
  toJSON _ = toJSON () -- Shouldn't happen

instance FromJSON (Some Empty) where
  parseJSON v = typeMismatch "Some (Empty _)" v

instance ArgDict Empty where
  type ConstraintsFor c Empty = ()
  argDict _ = error "argDict applied for Empty"

instance ShowTag Empty h where
  showTaggedPrec _ _ = error "showTaggedPrec applied for Empty" -- Shouldn't happen