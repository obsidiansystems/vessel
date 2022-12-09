{-# LANGUAGE AllowAmbiguousTypes #-}
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

module Data.Vessel.Class where

import Control.Arrow ((***))
import Control.Monad.Writer.Strict (Writer, execWriter, tell)
import Data.Align
import qualified Data.Dependent.Map as DMap'
import Data.Dependent.Map.Monoidal (MonoidalDMap(..))
import qualified Data.Dependent.Map.Monoidal as DMap
import Data.Foldable
import Data.Functor.Compose
import Data.Functor.Identity
import Data.GADT.Compare
import Data.Map.Monoidal (MonoidalMap(..))
import Data.Maybe (fromMaybe)
import Data.Proxy
import Data.Semigroup
import Data.These
import GHC.Generics
import Reflex.Query.Class
import Witherable

import Data.Vessel.Internal

------- The View Class -------

-- | Our containers are parameterised by a choice of functor to apply at the leaves of their
-- structure. By applying them to Identity, we obtain ordinary containers for data, called "views".
-- By applying them to Proxy, we obtain what are effectively blank forms to be filled in, called
-- "queries" or "view selectors". By using a functor such as Map k, information about many queries
-- or their results may be aggregated together into a single container.
--
-- This class codifies the operations we need to be able to perform on these container types in
-- order to transpose various Map-like structures into and out of them.
--
-- This is done for the purposes of, on the one hand collecting many users' view selectors into a
-- single aggregated selector containing information about who is interested in each part (condenseV),
-- and on the other hand, taking the resulting aggregated views and splitting them into a Map of
-- views for each user (disperseV).
--
-- It also specifies the cropV operation which restricts a view to a particular selection, as well
-- as operations for mapping functions over all the leaves of the container.
class View (v :: (x -> *) -> *) where
  -- | Transpose a sufficiently-Map-like structure into a container, effectively aggregating
  -- many structures into a single one containing information about which keys each part of it
  -- came from originally.
  condenseV :: (Foldable t, Filterable t, Functor t) => t (v g) -> v (Compose t g)
  default condenseV :: GCondenseView t g v => t (v g) -> v (Compose t g)
  condenseV tvg = to $ condenseView $ from <$> tvg

  -- | Transpose a sufficiently-Map-like structure out of a container, the inverse of condenseV.
  disperseV :: (Align t) => v (Compose t g) -> t (v g)
  default disperseV :: GDisperseView t g v => v (Compose t g) -> t (v g)
  disperseV vtg = to <$> disperseView (from vtg)

  -- TODO: Decide whether mapV and traverseV are actually a good idea to provide.
  -- They may actually help people write operations which are inefficient.

  -- | Given a structure specifying a query, and a structure representing a view of data,
  -- restrict the view to only those parts which satisfy the query. (Essentially intersection of Maps.)
  cropV :: (forall a. s a -> i a -> r a) -> v s -> v i -> Maybe (v r)
  default cropV :: forall s i r. GZipView s i r v => (forall a. s a -> i a -> r a) -> v s -> v i -> Maybe (v r)
  cropV f vi vs = maybeEmptyView $ to $ zipView z (from vi) (from vs)
    where z :: forall v'. (View v', EmptyView v') => v' s -> v' i -> v' r
          z v'i v's = fromMaybe emptyV $ cropV f v'i v's

  -- | We also want a way to determine if the container is empty, because shipping empty containers
  -- around is a bad idea.
  nullV :: v i -> Bool
  default nullV :: forall i. GMapView i i v => v i -> Bool
  nullV v = getAll $ execWriter $
              mapViewM @i @i @(Rep (v i)) @(Rep (v i)) f (from v)
    where f :: View v' => v' i -> Writer All (v' i) -- TODO: strict writer is not strict enough,  use State or Writer.CPS
          f v' = tell (All $ nullV v') *> pure v'

  -- | Map a natural transformation over all the leaves of a container, changing the functor which
  -- has been applied.
  mapV :: (forall a. f a -> g a) -> v f -> v g
  default mapV :: GMapView f g v => (forall a. f a -> g a) -> v f -> v g
  mapV f vf = to $ mapView (mapV f) $ from vf

  -- | Traverse over the leaves of a container.
  traverseV :: (Applicative m) => (forall a. f a -> m (g a)) -> v f -> m (v g)
  default traverseV :: (GMapView f g v, Applicative m) => (forall a. f a -> m (g a)) -> v f -> m (v g)
  traverseV f vf = to <$> mapViewM (traverseV f) (from vf)

  -- | Map over all the leaves of a container, keeping only the 'Just' results
  -- and returing 'Nothing' if no leaves are kept.
  mapMaybeV :: (forall a. f a -> Maybe (g a)) -> v f -> Maybe (v g)
  default mapMaybeV :: forall f g. GMapView f g v => (forall a. f a -> Maybe (g a)) -> v f -> Maybe (v g)
  mapMaybeV f vf = maybeEmptyView $ to $ mapView z $ from vf
    where z :: forall v'. (View v', EmptyView v') => v' f -> v' g
          z v'f = fromMaybe emptyV $ mapMaybeV f v'f

  -- | Map over all the leaves of two containers, combining the leaves with the
  -- provided function, keeping only the 'Just' results and returing 'Nothing'
  -- if no leaves are kept.
  alignWithMaybeV :: (forall a. These (f a) (g a) -> Maybe (h a)) -> v f -> v g -> Maybe (v h)
  default alignWithMaybeV :: forall f g h. GZipView f g h v => (forall a. These (f a) (g a) -> Maybe (h a)) -> v f -> v g -> Maybe (v h)
  alignWithMaybeV f vf vg = maybeEmptyView $ to $ zipView z (from vf) (from vg)
    where z :: forall v'. (View v', EmptyView v') => v' f -> v' g -> v' h
          z v'f v'g = fromMaybe emptyV $ alignWithMaybeV f v'f v'g

  -- | Map over all the leaves of two containers, combining the leaves with the
  -- provided function
  alignWithV :: (forall a. These (f a) (g a) -> h a) -> v f -> v g -> v h
  default alignWithV :: GZipView f g h v => (forall a. These (f a) (g a) -> h a) -> v f -> v g -> v h
  alignWithV f vf vg = to $ zipView (alignWithV f) (from vf) (from vg)

-- | A type `v` supports EmptyView iff it is able to contain no information.
class View v => EmptyView v where
  -- Law: nullV emptyV == True
  --TODO: More laws
  emptyV :: v f

maybeEmptyView :: View v => v f -> Maybe (v f)
maybeEmptyView v = if nullV v then Nothing else Just v

------ Classes and Generic instances for Generic View instance ------

class Empty1 a where
  empty :: a p

instance Empty1 U1 where
  empty = U1

instance EmptyView v => Empty1 (K1 i (v f)) where
  empty = K1 emptyV

instance Empty1 a => Empty1 (M1 i t a) where
  empty = M1 empty

instance (Empty1 a, Empty1 b) => Empty1 (a :*: b) where
  empty = empty :*: empty

type GCondenseView t f v =
  ( Generic (v f)
  , Generic (v (Compose t f))
  , CondenseView t (Rep (v f)) (Rep (v (Compose t f)))
  )

class (Foldable t, Filterable t, Functor t) => CondenseView t vf vtf where
  condenseView :: t (vf p) -> vtf p

instance (Foldable t, Filterable t, Functor t) => CondenseView t U1 U1 where
  condenseView _ = U1

instance (View v, Foldable t, Filterable t, Functor t) => CondenseView t (K1 i (v f)) (K1 i (v (Compose t f))) where
  condenseView tvf = K1 $ condenseV $ unK1 <$> tvf

instance CondenseView t vf vtf => CondenseView t (M1 i t' vf) (M1 i t' vtf) where
  condenseView tvf = M1 $ condenseView $ unM1 <$> tvf

instance (CondenseView t avf avtf, CondenseView t bvf bvtf, Empty1 avf, Empty1 bvf) => CondenseView t (avf :*: bvf) (avtf :*: bvtf) where
  condenseView tvf = condenseView (getA <$> tvf) :*: condenseView (getB <$> tvf)
    where getA (a :*: _) = a
          getB (_ :*: b) = b

type GDisperseView t f v =
  ( Generic (v f)
  , Generic (v (Compose t f))
  , DisperseView t (Rep (v f)) (Rep (v (Compose t f)))
  )

class Align t => DisperseView t vf vtf where
  disperseView :: vtf p -> t (vf p)

instance Align t => DisperseView t U1 U1 where
  disperseView _ = nil

instance (View v, Align t) => DisperseView t (K1 i (v f)) (K1 i (v (Compose t f))) where
  disperseView (K1 vtf) = K1 <$> disperseV vtf

instance DisperseView t vf vtf => DisperseView t (M1 i t' vf) (M1 i t' vtf) where
  disperseView (M1 vf) = M1 <$> disperseView vf

instance (DisperseView t avf avtf, DisperseView t bvf bvtf, Empty1 avf, Empty1 bvf) => DisperseView t (avf :*: bvf) (avtf :*: bvtf) where
  disperseView (avtf :*: bvtf) = alignWith f (disperseView avtf) (disperseView bvtf)
    where f :: These (avf p) (bvf p) -> (avf :*: bvf) p
          f = \case
            This a -> a :*: empty
            That b -> empty :*: b
            These a b -> a :*: b

type GMapView f g v =
  ( Generic (v f)
  , Generic (v g)
  , MapView f g (Rep (v f)) (Rep (v g))
  )

class MapView f g vf vg where
  mapViewM
    :: Applicative m
    => (forall v'. (View v', EmptyView v') => v' f -> m (v' g))
    -> vf p
    -> m (vg p)

instance MapView f g V1 V1 where
  mapViewM _ = \case

instance MapView f g U1 U1 where
  mapViewM _ U1 = pure U1

instance (View v, EmptyView v) => MapView f g (K1 i (v f)) (K1 i (v g)) where
  mapViewM f (K1 vf) = K1 <$> f vf

instance MapView f g vf vg => MapView f g (M1 i t vf) (M1 i t vg) where
  mapViewM f (M1 vf) = M1 <$> mapViewM f vf

instance (MapView f g avf avg, MapView f g bvf bvg) => MapView f g (avf :*: bvf) (avg :*: bvg) where
  mapViewM f (avf :*: bvf) = (:*:)
    <$> mapViewM f avf
    <*> mapViewM f bvf

mapView
  :: MapView f g vf vg
  => (forall v'. (View v', EmptyView v') => v' f -> v' g)
  -> vf p
  -> vg p
mapView f vf = runIdentity $ mapViewM (\v'f -> Identity $ f v'f) vf

type GZipView f g h v =
  ( Generic (v f)
  , Generic (v g)
  , Generic (v h)
  , ZipView f g h (Rep (v f)) (Rep (v g)) (Rep (v h))
  )

class ZipView f g h vf vg vh where
  zipViewM
    :: Applicative m
    => (forall v'. (View v', EmptyView v') => v' f -> v' g -> m (v' h))
    -> vf p
    -> vg p
    -> m (vh p)

instance ZipView f g h V1 V1 V1 where
  zipViewM _ = \case

instance ZipView f g h U1 U1 U1 where
  zipViewM _ U1 U1 = pure U1

instance (View v, EmptyView v) => ZipView f g h (K1 i (v f)) (K1 i (v g)) (K1 i (v h)) where
  zipViewM f (K1 vf) (K1 vg) = K1 <$> f vf vg

instance ZipView f g h vf vg vh => ZipView f g h (M1 i t vf) (M1 i t vg) (M1 i t vh) where
  zipViewM f (M1 vf) (M1 vg) = M1 <$> zipViewM f vf vg

instance (ZipView f g h avf avg avh, ZipView f g h bvf bvg bvh) => ZipView f g h (avf :*: bvf) (avg :*: bvg) (avh :*: bvh) where
  zipViewM f (avf :*: bvf) (avg :*: bvg) = (:*:)
    <$> zipViewM f avf avg
    <*> zipViewM f bvf bvg

zipView
  :: ZipView f g h vf vg vh
  => (forall v'. (View v', EmptyView v') => v' f -> v' g -> v' h)
  -> vf p
  -> vg p
  -> vh p
zipView f vf vg = runIdentity $ zipViewM (\v'f v'g -> Identity $ f v'f v'g) vf vg

collapseNullV :: View v => v f -> Maybe (v f)
collapseNullV v = if nullV v
  then Nothing
  else Just v


subtractV :: View v => v f -> v g -> Maybe (v f)
subtractV = alignWithMaybeV (\case This x -> Just x; _ -> Nothing)

alignWithMV
  :: forall m v f g h
  .  (View v, Applicative m)
  => (forall a. These (f a) (g a) -> m (h a))
  -> v f
  -> v g
  -> m (Maybe (v h))
alignWithMV f a b = traverse (traverseV getCompose) $ alignWithMaybeV g a b
  where g :: forall a. These (f a) (g a) -> Maybe (Compose m h a)
        g = Just . Compose . f

-- | A main point of the View class is to be able to produce this QueryMorphism.
transposeView
  :: ( View v
     , Foldable t
     , Filterable t
     , Functor t
     , Align t
     , QueryResult (t (v g)) ~ (t (v g'))
     , QueryResult (v (Compose t g)) ~ v (Compose t g')
     , Monoid (v g)
     , Monoid (v (Compose t g))
     )
  => QueryMorphism (t (v g)) (v (Compose t g))
transposeView = QueryMorphism
  { _queryMorphism_mapQuery = condenseV -- aggregate queries.
  , _queryMorphism_mapQueryResult = disperseV -- individualise results.
  }

mapDecomposedV
  :: (Functor m, View v)
  => (v Proxy -> m (v Identity))
  -> v (Compose (MonoidalMap c) g)
  -> m (Maybe (v (Compose (MonoidalMap c) Identity)))
mapDecomposedV f v = cropV recompose v <$> (f $ mapV (\_ -> Proxy) v)
  where
    recompose :: Compose (MonoidalMap c) g a -> Identity a -> Compose (MonoidalMap c) Identity a
    recompose (Compose s) i = Compose $ i <$ s

------- The View instance for MonoidalDMap -------
instance (GCompare k) => View (MonoidalDMap k) where
  cropV :: (forall a. s a -> i a -> r a) -> MonoidalDMap k s -> MonoidalDMap k i -> Maybe (MonoidalDMap k r)
  cropV f a b = collapseNullV $ DMap.intersectionWithKey (\_ s i -> f s i) a b

  nullV :: MonoidalDMap k s -> Bool
  nullV m = DMap.null m

  condenseV :: forall col g. ( Foldable col, Filterable col, Functor col )
            => col (MonoidalDMap k g)
            -> MonoidalDMap k (Compose col g)
  condenseV col = condenseD' (fold (fmap unMonoidalDMap col)) col

  disperseV :: forall col g. (Align col)
           => MonoidalDMap k (Compose col g)
           -> col (MonoidalDMap k g)
  disperseV row = case findPivotD (unMonoidalDMap row) of
    NoneD -> nil
    OneD k (Compose v) -> fmap (DMap.singleton k) v
    SplitD pivot _l _r -> uncurry (alignWith (mergeThese unionDistinctAscD)) $
      disperseV *** disperseV $ splitLTD pivot row

  mapV :: (forall a. f a -> g a) -> MonoidalDMap k f -> MonoidalDMap k g
  mapV f m = DMap.map f m

  traverseV :: (Applicative m) => (forall a. f a -> m (g a)) -> MonoidalDMap k f -> m (MonoidalDMap k g)
  traverseV f m = DMap.traverseWithKey (\_ v -> f v) m

  mapMaybeV f (MonoidalDMap m) = collapseNullV $ MonoidalDMap $
    DMap'.mapMaybe f m

  alignWithV f a b = alignWithKeyMonoidalDMap (\_ x -> f x) a b

  alignWithMaybeV f a b = collapseNullV $ alignWithKeyMaybeMonoidalDMap (\_ x -> f x) a b

instance (GCompare k) => EmptyView (MonoidalDMap k) where
  emptyV = DMap.empty

filterV :: View v => (forall a. f a -> Bool) -> v f -> Maybe (v f)
filterV f = mapMaybeV (\x -> if f x then Just x else Nothing)

-- | a completely empty view.
instance View Proxy
