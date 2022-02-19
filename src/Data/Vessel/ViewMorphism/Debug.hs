{-# LANGUAGE FlexibleContexts #-}
module Data.Vessel.ViewMorphism.Debug where

import Debug.Trace
import Data.Vessel.ViewMorphism

traceViewMorphism
  :: (Monad f, Show a, Monad g, Show b, Show (ViewQueryResult b), Show (ViewQueryResult a))
  => String -> ViewHalfMorphism f g a b -> ViewHalfMorphism f g a b
traceViewMorphism hint (ViewHalfMorphism f g) = ViewHalfMorphism
  (\x -> do
    traceM $ unwords ["traceViewMorphism ", hint, " query: ", show x]
    res <- f x
    traceM  $ unwords ["traceViewMorphism ", hint, " query: ", show x, "==", show res]
    pure res)
  (\x -> do
    traceM  $ unwords ["traceViewMorphism ", hint, " result: ", show x]
    res <- g x
    traceM  $ unwords ["traceViewMorphism ", hint, " result: ", show x, "==", show res]
    pure res)


