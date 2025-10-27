{-# LANGUAGE UndecidableInstances #-}
module Bench where

import Base

import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import System.Directory
import Test.QuickCheck (Property, discard, Arbitrary, property, witness)

import Language.Problem
import Language.Parser
import Language.Expr
import Synth

import Bench.Model qualified as Model

trySynthesize :: Arguments -> Problem -> Maybe (Program Void)
trySynthesize args problem = case synthesize args problem of
  Failure Depleted -> Nothing
  Failure Exhausted -> Nothing
  Success ((_, Unfinished _filling) :| _) -> Nothing
  Success ((_, Finished program) :| _)
    | testProblem program problem -> Just program
    | otherwise -> Nothing

testSynthesis :: Arguments -> Problem -> Model -> Property
testSynthesis args problem (Model model) = case trySynthesize args problem of
  Nothing -> discard
  Just program -> comparison model (interpret program)

loadProblem :: Name -> IO Problem
loadProblem name = do
  content <- Text.readFile $ "data/bench/" <> Text.unpack name.getName
  case lexParse (parser @(Named Problem)) content of
    Nothing -> error $ "Failed to parse " <> show (pretty name)
    Just problem -> return problem.value

loadAll :: IO [Named Problem]
loadAll = do
  xs <- listDirectory "data/bench/"
  forM (reverse xs) \name -> do
    content <- Text.readFile $ "data/bench/" <> name
    case lexParse (parser @(Named Problem)) content of
      Nothing -> error $ "Failed to parse " <> show (pretty name)
      Just problem -> return problem

class Compare a where
  comparison :: a -> a -> Property

instance {-# OVERLAPPABLE #-} (ToValue a, Eq a) => Compare a where
  comparison x y = witness (toValue a x) . witness (toValue a y) $ property $ x == y

instance {-# OVERLAPPABLE #-} (ToValue a, Arbitrary a, Show a, Compare b) =>
  Compare (a -> b) where
  comparison f g = property \x -> witness (toValue a x) $ comparison (f x) (g x)

data Model = forall a. (Compare a, Interpret a, Execute a) => Model a

-- NOTE: to check whether the models agree with the bench examples, they have to have the same type instantiation.
-- we decided to instantiate all models at Nat (except for tree leaves, which we instantiate at ())
-- this means that all benchmarks examples should also be defined in terms of natural numbers.
models :: [Named [Named Model]]
models =
  [ Named "simple"
    [ Named "append"            . Model $ Model.append @Nat
    , Named "concat"            . Model $ Model.concat @Nat
    , Named "drop"              . Model $ Model.drop @Nat
    , Named "head"              . Model $ Model.head @Nat
    , Named "index"             . Model $ Model.index @Nat
    , Named "init"              . Model $ Model.init @Nat
    , Named "last"              . Model $ Model.last @Nat
    , Named "length"            . Model $ Model.length @Nat
    , Named "null"              . Model $ Model.null @Nat
    , Named "prepend"           . Model $ Model.prepend @Nat
    , Named "reverse"           . Model $ Model.reverse @Nat
    , Named "splitAt"           . Model $ Model.splitAt @Nat
    , Named "tail"              . Model $ Model.tail @Nat
    , Named "take"              . Model $ Model.take @Nat
    , Named "unzip"             . Model $ Model.unzip @Nat @Nat
    , Named "zip"               . Model $ Model.zip @Nat @Nat
    ]

  , Named "extra"
    [ Named "cartesian"         . Model $ Model.cartesian @Nat
    , Named "copyFirst"         . Model $ Model.copyFirst @Nat
    , Named "copyLast"          . Model $ Model.copyLast @Nat
    , Named "shiftl"            . Model $ Model.shiftl @Nat
    , Named "shiftr"            . Model $ Model.shiftr @Nat
    , Named "partition"         . Model $ Model.partition @Nat @Nat
    ]

  , Named "trees"
    [ Named "breadthFirst"      . Model $ Model.breadthFirst @Nat @()
    , Named "depth"             . Model $ Model.depth @Nat @()
    , Named "inorder"           . Model $ Model.inorder @Nat @()
    , Named "levels"            . Model $ Model.levels @Nat @()
    , Named "mirror"            . Model $ Model.mirror @Nat @()
    , Named "size"              . Model $ Model.size @Nat @()
    ]

  , Named "eq"
    [ Named "compress"          . Model $ Model.compress @Nat
    , Named "group"             . Model $ Model.group @Nat
    , Named "elem"              . Model $ Model.elem @Nat
    , Named "elemIndex"         . Model $ Model.elemIndex @Nat
    , Named "nub"               . Model $ Model.nub @Nat
    , Named "union"             . Model $ Model.union @Nat
    ]

  , Named "ord"
    [ Named "insert"            . Model $ Model.insert @Nat
    , Named "maximum"           . Model $ Model.maximum @Nat
    , Named "ordNub"            . Model $ Model.ordNub @Nat
    , Named "pivot"             . Model $ Model.pivot @Nat
    , Named "sort"              . Model $ Model.sort @Nat
    , Named "sorted"            . Model $ Model.sorted @Nat
    ]
  ]
