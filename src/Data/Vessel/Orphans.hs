{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Vessel.Orphans () where

import Control.Arrow (Kleisli(..))
import Data.These (these, These(..))
import Data.These.Combinators
import Data.Void
import qualified Control.Categorical.Bifunctor as Cat
import qualified Control.Category.Associative as Cat
import qualified Control.Category.Braided as Cat
import qualified Control.Category.Monoidal as Cat
import qualified Data.Bitraversable as Base

instance Cat.PFunctor These (->) (->) where
  first = mapHere
instance Cat.QFunctor These (->) (->) where
  second = mapThere
instance Cat.Bifunctor These (->) (->) (->) where
  bimap = bimapThese
instance Cat.Associative (->) These where
  associate = assocThese
  disassociate = unassocThese

instance Cat.Monoidal (->) These where
  type Id (->) These = Void
  idl = these absurd id absurd
  idr = these id absurd (const absurd)
  coidl = That
  coidr = This

instance Cat.Braided (->) These where
  braid = swapThese

instance Cat.Symmetric (->) These



-- $Kleisli m$ preserves most structure,
instance (Base.Bitraversable p, Monad m) => Cat.PFunctor p (Kleisli m) (Kleisli m) where
  first (Kleisli f) = Kleisli $ Base.bitraverse f pure
instance (Base.Bitraversable p, Monad m) => Cat.QFunctor p (Kleisli m) (Kleisli m) where
  second (Kleisli g) = Kleisli $ Base.bitraverse pure g
instance (Base.Bitraversable p, Monad m) => Cat.Bifunctor p (Kleisli m) (Kleisli m) (Kleisli m) where
  bimap (Kleisli f) (Kleisli g) = Kleisli $ Base.bitraverse f g
instance (Cat.Associative (->) p, Base.Bitraversable p, Monad m) => Cat.Associative (Kleisli m) p where
  associate = Kleisli $ pure . Cat.associate
  disassociate = Kleisli $ pure . Cat.disassociate
instance (Base.Bitraversable p, Cat.Associative (->) p, Cat.Braided (->) p, Monad m) => Cat.Braided (Kleisli m) p where
  braid = Kleisli $ pure . Cat.braid
instance (Cat.Symmetric (->) p, Base.Bitraversable p, Cat.Braided (->) p, Monad m) => Cat.Symmetric (Kleisli m) p
instance (Cat.Monoidal (->) p, Base.Bitraversable p, Monad m) => Cat.Monoidal (Kleisli m) p where
  type Id (Kleisli m) p = Cat.Id (->) p
  idl = Kleisli $ pure . Cat.idl
  idr = Kleisli $ pure . Cat.idr
  coidl = Kleisli $ pure . Cat.coidl
  coidr = Kleisli $ pure . Cat.coidr

