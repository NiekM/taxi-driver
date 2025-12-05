module Utils
  ( altMap
  , withdraw, inject
  , gather
  , nubOn
  , vacate
  , enumerate
  ) where

import Data.Map.Strict qualified as Map
import Data.List (sortOn)
import Data.List.NonEmpty qualified as NonEmpty
import Control.Applicative
import Control.Carrier.State.Strict
import Data.Monoid (Alt(..))

import Base

altMap :: (Foldable f, Alternative m) => (a -> m b) -> f a -> m b
altMap f = getAlt . foldMap (Alt . f)

withdraw :: (Traversable f, Ord k) => f (k, v) -> (f k, Map k v)
withdraw = swap . traverse \(x, y) -> (Map.singleton x y, x)

inject :: (Traversable f, Ord k) => Map k v -> f k -> Maybe (f v)
inject m = traverse (`Map.lookup` m)

gather :: Ord k => [(k, v)] -> Map k (NonEmpty v)
gather xs = Map.fromList $ NonEmpty.groupAllWith fst xs <&> \ys ->
  (fst (NonEmpty.head ys), snd <$> ys)

nubOn :: Ord b => (a -> b) -> [a] -> [a]
nubOn f = map snd . sortOn fst . map NonEmpty.head . NonEmpty.groupAllWith (f . snd) . zip [0 :: Int ..]

vacate :: Traversable f => f a -> Maybe (f Void)
vacate = traverse $ const Nothing

enumerate :: Traversable t => t a -> t (Nat, a)
enumerate t = run $ evalState @Nat 0 do
  t & traverse \x -> do
    n <- get
    put (n + 1)
    return (n, x)
