{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Language.Spec where

import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set qualified as Set
import Data.Map qualified as Map
import Data.Functor qualified as Functor

import Base
import Language.Expr
import Language.Type
import Utils

-- A monomorphic input-output example according to some function signature. We
-- do not have to give a specific type instantiation, because we may make the
-- type more or less abstract. In other words, it is not up to the example to
-- decide which type abstraction we pick.
data Example = Example
  { inputs :: [Value]
  , output :: Value
  } deriving stock (Eq, Ord, Show)

-- | A declaration consists of a signature with some bindings.
data Spec = Spec
  { signature :: Signature
  , examples  :: [Example]
  } deriving stock (Eq, Ord, Show)

evaluate :: Program Void -> Spec -> Maybe [Value]
evaluate program spec = forM spec.examples \example ->
  let
    inputs = map Value example.inputs
    vars = map (.name) spec.signature.inputs
    expr = Apps (Lams vars program) inputs
  in case normalize expr of
    Value output -> Just output
    _ -> Nothing

testSpec :: Program Void -> Spec -> Bool
testSpec program spec = spec.examples & all \example ->
  let
    inputs = map Value example.inputs
    expr = Apps program inputs
  in case normalize expr of
    Value output | output == example.output -> True
    _ -> False

data Arg = Arg
  { mono  :: Mono
  , terms :: [Value]
  } deriving stock (Eq, Ord, Show)

data Args = Args
  { inputs :: [Named Arg]
  , output :: Arg
  } deriving stock (Eq, Ord, Show)

toArgs :: Spec -> Args
toArgs (Spec signature examples) = Args
  { inputs = zipWith (fmap . flip Arg) (inputs ++ repeat []) signature.inputs
  , output = Arg signature.output outputs
  } where
    (inputs, outputs) = first List.transpose . unzip
      $ examples <&> \ex -> (ex.inputs, ex.output)

fromArgs :: [Constraint] -> Args -> Spec
fromArgs constraints (Args inputs (Arg goal outputs)) = Spec
  { signature = Signature
    { constraints
    , inputs = inputs <&> fmap (.mono)
    , output = goal
    }
  , examples = zipWith Example (exInputs ++ repeat []) outputs
  } where
    exInputs = List.transpose $ map (.value.terms) inputs

onArgs :: (Args -> Args) -> Spec -> Spec
onArgs f p = fromArgs p.signature.constraints . f $ toArgs p

-- Check the realizability of a set of input-output examples (ignoring the types)
-- Returns conflicting examples.
monoCheck :: Spec -> Maybe (NonEmpty (NonEmpty Example))
monoCheck p = NonEmpty.nonEmpty $ filter inconsistent sameInputs
  where
    inconsistent (x :| xs) = any (/= x) xs
    sameInputs = NonEmpty.groupAllWith (.inputs) p.examples

disable :: Set Name -> Args -> Args
disable ss args = args { inputs = map enable args.inputs }
  where
    enable (Named name arg)
      | name `Set.notMember` ss = Named name arg
      | otherwise = Named name . Arg (Free "_") $ Unit <$ arg.terms

variables :: Spec -> [Name]
variables spec = spec.signature.inputs <&> (.name)

hide :: [Name] -> Spec -> Spec
hide names = onArgs \args -> args
  { inputs = filter (\arg -> arg.name `notElem` names) args.inputs }

addInputs :: [Named Arg] -> Spec -> Spec
addInputs new = onArgs \args -> args { inputs = args.inputs ++ new }

inputArgs :: Spec -> [Named Arg]
inputArgs spec = (toArgs spec).inputs

outputArg :: Spec -> Arg
outputArg spec = (toArgs spec).output

named :: [Named a] -> Map Name a
named = Map.fromList . map \x -> (x.name, x.value)

split :: DataContext -> Arg -> Spec -> Either Text (Map Name (Arg, Spec))
split ctx (Arg (Data d ts) terms) (Spec signature examples) = do
  fields <- forM terms \case
    Ctr c x -> Right (c, x)
    _ -> Left "field is not a constructor"
  let
    cs = named $ getConstructors d ts ctx
    paired = zipWith (fmap . (,)) examples fields
    m = NonEmpty.toList <$> gather paired
    (exs, vals) = Functor.unzip $ unzip <$> Map.union m ([] <$ cs)
    args = Map.intersectionWith Arg cs vals
    prbs = Spec signature <$> exs
  return $ Map.intersectionWith (,) args prbs
split _ _ _ = Left "argument is not a datatype"

instance Project Example where
  projections (Example ins out) = Example ins <$> projections out

instance Project Spec where
  projections prob = zipWith Spec ss (bs ++ repeat [])
    where
      ss = projections prob.signature
      bs = List.transpose $ map projections prob.examples

instance Project Arg where
  projections = \case
    Arg (Product ts) es ->
      zipWith Arg ts . (++ repeat []) . List.transpose $ map projections es
    a -> [a]
