module Bench.Model where

import Base

import Data.Either qualified as Either
import Data.Ord qualified as Ord
import Data.Tree.Binary
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Test.QuickCheck (SortedList(..))

allSame :: Eq a => [a] -> Bool
allSame [] = True
allSame (x:xs) = all (== x) xs

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

clamp :: Ord a => a -> a -> a -> a
clamp x y = Ord.clamp (x, y)

compress :: Eq a => [a] -> [a]
compress = map NonEmpty.head . NonEmpty.group

concat :: [[a]] -> [a]
concat = List.concat

cons :: a -> [a] -> [a]
cons = (:)

copyFirst :: [a] -> [a]
copyFirst [] = []
copyFirst xs@(x:_) = map (const x) xs

copyLast :: [a] -> [a]
copyLast [] = []
copyLast xs = map (const $ List.last xs) xs

deleteMax :: Ord a => [a] -> [a]
deleteMax [] = []
deleteMax xs = List.filter (/= List.maximum xs) xs

depth :: Tree a b -> Nat
depth (Leaf _) = 0
depth (Node l _ r) = 1 + max (depth l) (depth r)

drop :: Nat -> [a] -> [a]
drop = List.genericDrop

dupli :: [a] -> [a]
dupli = concatMap \x -> [x, x]

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

insert :: Ord a => a -> SortedList a -> [a]
insert x (Sorted xs) = List.insert x xs

last :: [a] -> Maybe a
last [] = Nothing
last xs = Just $ List.last xs

length :: [a] -> Nat
length = List.genericLength

longZip :: Semigroup m => [m] -> [m] -> [m]
longZip xs [] = xs
longZip [] ys = ys
longZip (x:xs) (y:ys) = x <> y : longZip xs ys

levels :: Tree a b -> [[a]]
levels (Leaf _) = []
levels (Node l x r) = [x] : longZip (levels l) (levels r)

maximum :: Ord a => [a] -> Maybe a
maximum [] = Nothing
maximum xs = Just $ List.maximum xs

prepend :: [a] -> [a] -> [a]
prepend = flip (++)

elem :: Eq a => a -> [a] -> Bool
elem = List.elem

elemIndex :: Eq a => a -> [a] -> Maybe Nat
elemIndex x = fmap fromIntegral . List.elemIndex x

mostCommon :: Eq a => [a] -> Maybe a
mostCommon = pickMax . foldr add []
  where
    pickMax :: [(a, Int)] -> Maybe a
    pickMax ys = fst <$> List.find ((== n) . snd) ys
      where n = List.maximum $ map snd ys

    add :: Eq a => a -> [(a, Int)] -> [(a, Int)]
    add x [] = [(x, 1)]
    add x ((y, n):ys)
      | x == y = (y, n + 1) : ys
      | otherwise = (y, n) : add x ys

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

preorder :: Tree a b -> [a]
preorder (Leaf _) = []
preorder (Node l x r) = x : preorder l ++ preorder r

replicate :: Nat -> a -> [a]
replicate = List.replicate . fromIntegral

reverse :: [a] -> [a]
reverse = List.reverse

setInsert :: Ord a => a -> [a] -> [a]
setInsert x = List.nub . List.insert x

shiftl :: [a] -> [a]
shiftl [] = []
shiftl (x:xs) = xs ++ [x]

shiftr :: [a] -> [a]
shiftr [] = []
shiftr xs = List.last xs : List.init xs

size :: Tree a b -> Nat
size (Leaf _) = 0
size (Node l _ r) = 1 + size l + size r

mirror :: Tree a b -> Tree a b
mirror (Leaf x) = Leaf x
mirror (Node l x r) = Node (mirror r) x (mirror l)

snoc :: a -> [a] -> [a]
snoc x xs = xs ++ [x]

sort :: Ord a => [a] -> [a]
sort = List.sort

sorted :: Ord a => [a] -> Bool
sorted [] = True
sorted (x:xs) = List.and $ List.zipWith (<=) (x:xs) xs

splitAt :: Nat -> [a] -> ([a], [a])
splitAt = List.genericSplitAt

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

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
