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

module Data.Vessel.Disperse where

import Control.Arrow ((***))
import Data.Witherable
import Data.Align
import Data.Map.Monoidal (MonoidalMap (..))
import qualified Data.Map.Monoidal as Map
import Data.These
import Data.Foldable hiding (null)

import Data.Vessel.Internal

-- | Disperse is a simplified version of View for ordinary containers. This is used as a stepping stone to obtain the View instance for MapV.
class Disperse row where
  disperse :: (Foldable col, Filterable col, Functor col) => col (row a) -> row (col a)
  condense :: (Align col) => row (col a) -> col (row a)

instance Ord k => Disperse (MonoidalMap k) where
  disperse :: forall col a. (Foldable col, Filterable col, Functor col)
           => col (MonoidalMap k a)
           -> MonoidalMap k (col a)
  disperse col = disperse' (Map.MonoidalMap (fold (fmap Map.getMonoidalMap col))) col
    where
      disperse'
        :: MonoidalMap k a
        -> col (MonoidalMap k a)
        -> MonoidalMap k (col a)
      disperse' folded col' = case findPivot folded of
        None -> Map.MonoidalMap mempty
        One k _ -> Map.singleton k (mapMaybe (Map.lookup k) col')
        Split pivot l r -> uncurry unionDistinctAsc $ (disperse' l *** disperse' r) $ split pivot col'
      split
        :: (Ord k, Filterable col)
        => k -> col (MonoidalMap k a)
        -> (col (MonoidalMap k a), col (MonoidalMap k a))
      split pivot col' = unalignProperly $ mapMaybe (splitOne pivot) col'
      splitOne
        :: Ord k
        => k
        -> MonoidalMap k a
        -> Maybe (These (MonoidalMap k a) (MonoidalMap k a))
      splitOne pivot m =
        let (l, r) = splitLT pivot m
        in case (Map.null l, Map.null r) of
          (True, True) -> Nothing
          (False, True) -> Just $ This l
          (True, False) -> Just $ That r
          (False, False) -> Just $ These l r

  condense :: forall col a. (Align col)
           => MonoidalMap k (col a)
           -> col (MonoidalMap k a)
  condense row = case findPivot row of
    None -> nil
    One k v -> fmap (Map.singleton k) v
    Split pivot _l _r -> uncurry (alignWith (mergeThese unionDistinctAsc)) $ condense *** condense $ splitLT pivot row

instance Disperse Maybe where
  disperse xs =
    let xs' = catMaybes xs
    in if null xs' then Nothing else Just xs'
  condense = \case
    Nothing -> nil
    Just xs -> Just <$> xs
