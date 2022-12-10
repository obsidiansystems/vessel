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

module Data.Vessel.Selectable where
------- Selectable convenience class -------

import Data.Functor.Identity

-- A convenience class for producing and consuming functor-indexed containers.
class Selectable v k where
  -- | A more convenient type to use for extracting results.
  type Selection v k
  -- | Build a query given a suitable value for specifying what we're asking for.
  -- 'p' will typically be Proxy or Const SelectedCount.
  selector :: (forall a. p a) -> k -> v p
  -- | From a view, extract a more convenient type of value to use.
  selection :: k -> v Identity -> Selection v k
