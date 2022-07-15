{-# LANGUAGE FlexibleContexts #-}
module Data.Vessel.ViewMorphism.Cartesian where

import Control.Applicative
import Control.Category
import Data.Align
import Data.These (these, These(..))
import Prelude hiding ((.), id)

import Data.Vessel.ViewMorphism


import qualified Control.Category.Cartesian as Cat

inlV :: (Applicative f, Applicative g, Alternative g) => ViewHalfMorphism f g a (These a b)
inlV = ViewHalfMorphism (pure . This) (these pure (const empty) (const . pure))

inrV :: (Applicative f, Applicative g, Alternative g) => ViewHalfMorphism f g b (These a b)
inrV = ViewHalfMorphism (pure . That) (these (const empty) pure (const pure))

(|||^)
  :: (Applicative f, Alternative g, Monad g, Semigroup c)
  => ViewHalfMorphism f g a c
  -> ViewHalfMorphism f g b c
  -> ViewHalfMorphism f g (These a b) c
ViewHalfMorphism f f' |||^ ViewHalfMorphism g g' = ViewHalfMorphism
  (these f g $ \x y -> liftA2 (<>) (f x) (g y))
  (\x -> do
    x' <- Just <$> f' x <|> pure Nothing
    x'' <- Just <$> g' x <|> pure Nothing
    maybe empty pure $ align x' x''
  )

codiagV :: (Applicative f, Applicative g, Semigroup a) => ViewHalfMorphism f g (These a a) a
codiagV = ViewHalfMorphism
  (pure . these id id (<>))
  (pure . uncurry These . Cat.diag)

fstV :: (Alternative f, Applicative g) => ViewHalfMorphism f g (These a b) a
fstV = ViewHalfMorphism (these pure (const empty) (const . pure)) (pure . This)

sndV :: (Alternative f, Applicative g) => ViewHalfMorphism f g (These a b) b
sndV = ViewHalfMorphism (these (const empty) pure (const pure)) (pure . That)

(&&&^)
  :: (Monad f, Alternative f, Applicative g, Semigroup (ViewQueryResult a))
  => ViewHalfMorphism f g a b
  -> ViewHalfMorphism f g a c
  -> ViewHalfMorphism f g a (These b c)
ViewHalfMorphism f f' &&&^ ViewHalfMorphism g g' = ViewHalfMorphism
  (\x -> do
    x' <- Just <$> f x <|> pure Nothing
    x'' <- Just <$> g x <|> pure Nothing
    maybe empty pure $ align x' x''
  )
  (these f' g' $ \x y -> liftA2 (<>) (f' x) (g' y))

diagV :: (Applicative f, Applicative g, Semigroup (ViewQueryResult a)) => ViewHalfMorphism f g a (These a a)
diagV = ViewHalfMorphism
  (pure . uncurry These . Cat.diag)
  (pure . these id id (<>))

