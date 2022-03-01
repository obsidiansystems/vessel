{-# Language FlexibleInstances #-}
{-# Language FunctionalDependencies #-}
{-# Language RankNTypes #-}
{-# Language GADTs #-}
module Data.Vessel.Path where

import Control.Applicative
import Control.Monad
import Control.Monad.Fix
import qualified Data.Dependent.Map.Monoidal as MonoidalDMap
import Data.GADT.Compare
import Data.Map (Map)
import Data.Functor.Identity (Identity(..))
import qualified Data.Map as Map
import Data.Map.Monoidal
import Data.Semigroup (First(..))
import Data.Set (Set)
import Data.Vessel.Class hiding (mapV)
import Data.Vessel.DependentMap hiding (dmapV)
import Data.Vessel.Identity hiding (identityV)
import Data.Vessel.Map hiding (mapV)
import Data.Vessel.Single hiding (singleV)
import Data.Vessel.SubVessel hiding (subVessel)
import Data.Vessel.Vessel hiding (vessel)
import Data.Vessel.ViewMorphism (ViewMorphism(..), ViewHalfMorphism(..), ViewQueryResult)
import Reflex

-- | A (Path v w w' v') consists of maps in opposite directions:
--
--  >        v ---> w
--  > Maybe v' <--- w'
--
--  If we think of v / v' as variants of a "small" structure, and w / w' as
--  variants of a "large" structure, this encodes how to on the one hand
--  include v inside a larger structure of type w, and how to (potentially)
--  extract a value of type v' from a structure of type w'.
--
--  Vessels are often used to represent queries and their responses. It may be
--  useful to think of @v@ as being some small part of a query, @w@ as being a
--  larger or more complete query, @w'@ as being a complete response, and @v'@
--  as being the smaller part of the response corresponding to @v@.
--
-- In this way, we can package up parts of the query/response round-trip,
-- and not have to specify twice at which keys we're querying on the one hand
-- and looking up on the other.
--
-- Each @Path@ will often be a pair of the "singleton" constructor of some sort of
-- map-like datastructure and its corresponding lookup.
--
--  For example, given @MapV k v@, @key k@ will produce a @Path@ that describes
--  how to construct a singleton @MapV@ and how to extract the value at key @k@
--  from a @MapV@.
--
--  This becomes particularly useful as your vessels become more complicated.
--  For example given a @SubVessel k (MapV k' a) g@, you can construct a path
--  such as @key k ~> key k'@ that constructs a singleton of a singleton and,
--  in the other direction, looks up the @MapV@ at key @k@ of the @SubVessel@
--  and the value at key @k'@ of the @MapV@.
--
--  Formally, these are arrows in the product category of Hask and the Kleisli
--  category of Maybe.
data Path v w w' v' = Path { _path_to :: v -> w, _path_from :: w' -> Maybe v' }

-- | Compose two paths
(~>) :: Path b c c' b' -> Path a b b' a' -> Path a c c' a'
Path to from ~> Path to' from' = Path (to . to') (from' <=< from)

-- | The identity path
idP :: Path a a b b
idP = Path id pure

-- | Construct a @Path@ which uses the given function on the "input" or "query" side
-- and does nothing on the output side.
preMap :: (a -> b) -> Path a b x x
preMap f = Path f pure

-- | Construct a @Path@ which uses the given function on the "output" or "response" side
-- and does nothing on the input side. Useful for post-processing the results of queries.
postMap :: (a' -> Maybe b') -> Path x x a' b'
postMap f = Path id f

-- | A class for keyed map-like datastructures of various types, giving an appropriate
-- @Path@ for constructing a singleton at the given key, and for extracting the value at
-- that key, if any.
class Keyed k a b b' a'  | k b -> a, k b' -> a' where
  key :: k -> Path a b b' a'

-- | A class for keyed map-like datastructures of various types, giving an appropriate
-- @Path@ for constructing a mapping having the given set of keys, with the same value
-- at every key, and for extracting the restriction of the corresponding map to the given keys.
class SetKeyed k a b b' a'  | k b -> a, k b' -> a' where
  keys :: Set k -> Path a b b' a'

instance (GCompare k, View v) => Keyed (k v) (v g) (Vessel k g) (Vessel k g') (v g') where
  key = vessel

instance (Ord k, View v) => Keyed k (v g) (SubVessel k v g) (SubVessel k v g') (v g') where
  key = subVessel

instance (Ord k) => Keyed k (g v) (MapV k v g) (MapV k v g') (g' v) where
  key = mapV

instance (GCompare k) => Keyed (k a) (g (v a)) (DMapV k v g) (DMapV k v g') (g' (v a)) where
  key = dmapV

instance (Ord k, Applicative g') => SetKeyed k (g v) (MapV k v g) (MapV k v g') (g' (Map k v)) where
  keys = mapVSet

-- | This is the implementation of @key@ for @Vessel@. Given some key of type @k v@, gives a @Path@
-- that on the one hand will transform a value of type @v g@ into a complete singleton @Vessel@
-- and in the other direction, will perform a lookup for the given key on a similar @Vessel@.
vessel :: (GCompare k, View v) => k v -> Path (v g) (Vessel k g) (Vessel k g') (v g')
vessel k = Path { _path_to = singletonV k, _path_from = lookupV k }

-- | This is the implementation of @key@ for @SubVessel@. Given some key of type @k@, gives a @Path@
-- that on the one hand will transform a value of type @v g@ into a complete singleton @SubVessel@
-- and in the other direction, will perform a lookup for the given key on a similar @SubVessel@.
subVessel :: (Ord k, View v) => k -> Path (v g) (SubVessel k v g) (SubVessel k v g') (v g')
subVessel k = Path { _path_to = singletonSubVessel k, _path_from = lookupSubVessel k }

-- | This is the implementation of @key@ for @MapV@. Given some key of type @k@, gives a @Path@
-- that on the one hand will transform a value of type @g v@ into a complete singleton @MapV@
-- and in the other direction, will perform a lookup for the given key on a similar @MapV@.
mapV :: (Ord k) => k -> Path (g v) (MapV k v g) (MapV k v g') (g' v)
mapV k = Path { _path_to = singletonMapV k, _path_from = lookupMapV k }

-- | This is the implementation of @keys@ for @MapV@. Given a set of keys of type @k@, gives a @Path@
-- that on the one hand will transform a value of type @g v@ into a @MapV@ having the given set of keys
-- and the given @g v@ at every key. In the other direction, it will perform a restrictKeys to select
-- the given keys out of the response of type @MapV k v g'@ and fully unpack the result into a
-- @g' (Map k v)@.
mapVSet :: (Ord k, Applicative g') => Set k -> Path (g v) (MapV k v g) (MapV k v g') (g' (Map k v))
mapVSet ks = Path
  { _path_to = \g -> MapV (MonoidalMap (Map.fromSet (const g) ks))
  , _path_from = Just . sequenceA . flip Map.restrictKeys ks . getMonoidalMap . unMapV
  }

-- | This is the implementation of @key@ for @DMapV@. Given some key of type @k a@, gives a @Path@
-- that on the one hand will transform a value of type @g (v a)@ into a complete singleton @DMapV@
-- and in the other direction, will perform a lookup for the given key on a similar @DMapV@.
dmapV :: (GCompare k) => k a -> Path (g (v a)) (DMapV k v g) (DMapV k v g') (g' (v a))
dmapV k = Path
  { _path_to = singletonDMapV k
  , _path_from = lookupDMapV k
  }

-- | This is a @Path@ which wraps/unwraps @IdentityV@. The unwrapping always succeeds of course.
identityV :: Path (g a) (IdentityV a g) (IdentityV a g') (g' a)
identityV = Path
  { _path_to = IdentityV
  , _path_from = Just . unIdentityV
  }

-- | This is a @Path@ which wraps/unwraps @SingleV@. Always produces a @SingleV@ containing @Just@ of
-- the input value on the input side, but unwrapping will result in @Just@ or @Nothing@ according to
-- whether the response contains a @Just@ or @Nothing@.
singleV :: (Traversable g', Functor g) => Path (g a) (SingleV a g) (SingleV a g') (g' a)
singleV = Path
  { _path_to = SingleV . fmap (First . Just)
  , _path_from = sequenceA . fmap getFirst . unSingleV
  }

-- | Combines two @Path@s whose full query type is a @Semigroup@, effectively, asking for two things at once,
-- and extracting the pair of results afterward.
zip :: (Semigroup c) => Path a c c' a' -> Path b c c' b' -> Path (a, b) c c' (a', b')
zip (Path to from) (Path to' from') = Path (\(x,y) -> to x <> to' y) (\c -> liftA2 (,) (from c) (from' c))

-- | A ViewMorphism can be used as a Path to a ViewQueryResult
vPath :: ViewMorphism Identity Maybe a b -> Path a b (ViewQueryResult b) (ViewQueryResult a)
vPath = vPath' . _viewMorphism_to

-- | A ViewHalfMorphism can be used as a Path to a ViewQueryResult
vPath' :: ViewHalfMorphism Identity Maybe a b -> Path a b (ViewQueryResult b) (ViewQueryResult a)
vPath' (ViewHalfMorphism f g) = Path (runIdentity . f) g

