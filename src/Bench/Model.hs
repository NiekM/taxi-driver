module Bench.Model where

import Base

import Data.Either qualified as Either
import Data.Tree.Binary
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Test.QuickCheck (SortedList(..))

append :: [a] -> [a] -> [a]
append = (++)

breadthFirst :: Tree a b -> [a]
breadthFirst = List.concat . levels

cartesian :: forall a. [[a]] -> [[a]]
cartesian xss = foldr f [[]] xss
  where
    f :: [a] -> [[a]] -> [[a]]
    f xs yss = foldr g [] xs
      where
        g :: a -> [[a]] -> [[a]]
        g x zss = foldr (\ys qss -> (x:ys):qss) zss yss

compress :: Eq a => [a] -> [a]
compress = map NonEmpty.head . NonEmpty.group

concat :: [[a]] -> [a]
concat = List.concat

copyFirst :: [a] -> [a]
copyFirst [] = []
copyFirst xs@(x:_) = map (const x) xs

copyLast :: [a] -> [a]
copyLast [] = []
copyLast xs = map (const $ List.last xs) xs

depth :: Tree a b -> Nat
depth (Leaf _) = 0
depth (Node l _ r) = 1 + max (depth l) (depth r)

drop :: Nat -> [a] -> [a]
drop = List.genericDrop

elem :: Eq a => a -> [a] -> Bool
elem = List.elem

elemIndex :: Eq a => a -> [a] -> Maybe Nat
elemIndex x = fmap fromIntegral . List.elemIndex x

group :: Eq a => [a] -> [[a]]
group = List.group

head :: [a] -> Maybe a
head [] = Nothing
head (x:_) = Just x

index :: Nat -> [a] -> Maybe a
index n = (List.!? fromIntegral n)

init :: [a] -> [a]
init [] = []
init xs = List.init xs

inorder :: Tree a b -> [a]
inorder (Leaf _) = []
inorder (Node l x r) = inorder l ++ x : inorder r

-- NOTE: we define insert in terms of SortedList so that QuickCheck only compares against this model solution using sorted inputs.
insert :: Ord a => a -> SortedList a -> [a]
insert x (Sorted xs) = List.insert x xs

last :: [a] -> Maybe a
last [] = Nothing
last xs = Just $ List.last xs

length :: [a] -> Nat
length = List.genericLength

levels :: Tree a b -> [[a]]
levels (Leaf _) = []
levels (Node l a r) = [a] : longZip (levels l) (levels r)
  where
    longZip :: Semigroup m => [m] -> [m] -> [m]
    longZip xs [] = xs
    longZip [] ys = ys
    longZip (x:xs) (y:ys) = x <> y : longZip xs ys

maximum :: Ord a => [a] -> Maybe a
maximum [] = Nothing
maximum xs = Just $ List.maximum xs

mirror :: Tree a b -> Tree a b
mirror (Leaf x) = Leaf x
mirror (Node l x r) = Node (mirror r) x (mirror l)

nub :: Eq a => [a] -> [a]
nub = List.nub

null :: [a] -> Bool
null = List.null

ordNub :: Ord a => [a] -> [a]
ordNub = List.nub . List.sort

partition :: [Either a b] -> ([a], [b])
partition = Either.partitionEithers

pivot :: Ord a => a -> [a] -> ([a], [a])
pivot x xs = (filter (< x) xs, filter (>= x) xs)

prepend :: [a] -> [a] -> [a]
prepend = flip (++)

reverse :: [a] -> [a]
reverse = List.reverse

shiftl :: [a] -> [a]
shiftl [] = []
shiftl (x:xs) = xs ++ [x]

shiftr :: [a] -> [a]
shiftr [] = []
shiftr xs = List.last xs : List.init xs

size :: Tree a b -> Nat
size (Leaf _) = 0
size (Node l _ r) = 1 + size l + size r

sort :: Ord a => [a] -> [a]
sort = List.sort

sorted :: Ord a => [a] -> Bool
sorted [] = True
sorted (x:xs) = List.and $ List.zipWith (<=) (x:xs) xs

splitAt :: Nat -> [a] -> ([a], [a])
splitAt = List.genericSplitAt

tail :: [a] -> [a]
tail [] = []
tail (_:xs) = xs

take :: Nat -> [a] -> [a]
take = List.genericTake

union :: Eq a => [a] -> [a] -> [a]
union = List.union

unzip :: [(a, b)] -> ([a], [b])
unzip = List.unzip

zip :: [a] -> [b] -> [(a, b)]
zip = List.zip
