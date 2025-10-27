{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Arbitrary where

import Base
import Data.Map qualified as Map
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Tree.Binary

import Test.QuickCheck hiding (total)
import Language.Type
import Language.Container
import Language.Expr
import Language.Problem

(|:) :: [a] -> a -> NonEmpty a
xs |: x = foldr NonEmpty.cons (pure x) xs

-- We assume n > 0
divyUp :: Nat -> Nat -> Gen (NonEmpty Nat)
divyUp total n = do
  cuts <- vectorOf (fromIntegral n - 1) $ choose (0, total)
  let starts = 0 :| List.sort cuts
  let ends = List.sort cuts |: total
  return $ NonEmpty.zipWith (-) ends starts

sizedMono :: [Name] -> Nat -> Gen Mono
sizedMono free size = case size of
  0 -> frequency . map (second pure) $
    [ (1, Top)
    -- , (2, Base Int)
    ] ++ [ (5, Free v) | v <- free ]
  n -> oneof . map snd $ filter fst
    [ (n >= 2,) $ Data "Tree" <$> do
      sizes <- divyUp (n - 2) 2
      forM (NonEmpty.toList sizes) (sizedMono free)
    , (True,) $ Data "List" . pure <$> sizedMono free (n - 1)
    , (True,) $ Data "Maybe" . pure <$> sizedMono free (n - 1)
    , (n == 1, pure $ Data "Bool" [])
    , (n >= 2,) do
      k <- choose (2, min n 3)
      sizes <- divyUp (n - k) k
      Product <$> forM (NonEmpty.toList sizes) (sizedMono free)
    ]

mono :: [Name] -> Gen Mono
mono free = sized \n -> choose (0, fromIntegral n) >>= sizedMono free

sig :: [Name] -> Gen Signature
sig free = do
  len <- frequency . map (second pure) $ [(1, 1), (2, 2), (1, 3)]
  ins <- replicateM len $ choose (0, 3) >>= sizedMono free
  output <- choose (0, 3) >>= sizedMono free
  let inputs = zipWith Named ["x", "y", "z"] ins
  return $ Signature [] inputs output

-- We assume that all free variables are instantiated as Int
constant :: Mono -> Gen Value
constant = \case
  Free _ -> error "Unexpected free variable"
  Base Int -> resize 3 $ Lit . MkInt <$> arbitrary
  Product ts -> Tuple <$> forM ts (scale (`div` length ts) . constant)
  Data "Bool" [] -> toExpr (type Bool) <$> arbitrary
  Data "Ordering" [] -> toExpr (type Ordering) <$> arbitrary
  Data "List" [t] -> toExpr (type [_]) <$> liftArbitrary
    (scale (`div` 2) $ constant t)
  Data "Maybe" [t] -> toExpr (type (Maybe _)) <$> liftArbitrary (constant t)
  Data "Tree" [t, u] -> toExpr (type (Tree _ _)) <$> liftArbitrary2
    (scale (`div` 2) $ constant t) (scale (`div` 2) $ constant u)
  Data t _ -> error $ "Datatype " <> show t <> " not supported"

instance Arbitrary Value where
  arbitrary = constant =<< resize 3 (mono [])

instance Arbitrary Name where
  arbitrary = sized \n -> do
    k <- choose (1, n + 1)
    fromString <$> vectorOf k do
      elements $ '_' : ['a' .. 'z']

instance Arbitrary1 Named where
  liftArbitrary arb = Named <$> arbitrary <*> arb

instance Arbitrary a => Arbitrary (Named a) where
  arbitrary = arbitrary1

constraint :: [Name] -> Gen Constraint
constraint free = do
  name <- elements free
  elements [Eq name, Ord name]

valueMap :: [Name] -> Gen (Map Position Value)
valueMap free = sized \n -> do
  Map.unions <$> forM free \name -> do
    t <- resize 3 $ mono []
    k <- choose (0, fromIntegral n)
    Map.fromList <$> forM [0 .. k] \i -> do
      (Named name i,) <$> constant t

-- TODO: we may want to generate examples that are more likely to be realizable.
-- For example, we could try to only generate signatures that are inhabited.
-- Perhaps more interestingly: decide beforehand whether an example should be
-- realizable, and ensure that around 50/50 are (un)realizable.
example :: Signature -> Gen Example
example signature = scale (`div` length signature.inputs) do
  let ty = Data "Ordering" []
  let arg = constant . instantiate (const ty)
  inputs <- forM signature.inputs \input -> arg input.value
  output <- arg signature.output
  return $ Example inputs output

problem :: [Name] -> Gen Problem
problem free = do
  signature <- sig free
  len <- frequency . map (second pure) $
    [ (2, 1)
    , (3, 2)
    , (2, 3)
    , (1, 4)
    , (1, 5)
    ]
  examples <- vectorOf len $ example signature
  return $ Problem signature examples
