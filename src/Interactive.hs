{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- NOTE: this module is only meant for opening in ghci.
module Interactive where

import GHC.Generics

import Data.Set qualified as Set
import Data.Map qualified as Map
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (fromJust, catMaybes)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import System.IO.Unsafe qualified as Unsafe
import System.Directory
import System.Timeout

import Control.Monad.Search
import Control.Carrier.Reader
import Control.Carrier.Choose.Church
import Control.Carrier.Error.Either
import Control.Effect.Fresh.Named
import Control.Carrier.State.Strict
import Data.String
import Prettyprinter

import Data.Tree.Binary

import Base
import Control.Effect.Search
import Data.Map.Multi qualified as Multi
import Language.Type
import Language.Expr
import Language.Container
import Language.Container.Morphism
import Language.Container.Relation
import Language.Coverage
import Language.Spec
import Language.Parser
import Language.Pretty
import Language.Prelude
import Utils

import Tactic
import Tactic.Combinators
import Tactic.Predicate
import Tactic.Ignore qualified as Tactic
import Tactic.Filter qualified as Tactic
import Tactic.Fold qualified as Tactic
import Tactic.Map qualified as Tactic
import Tactic.Relation qualified as Tactic
import Synth

import Test.QuickCheck hiding (Success, Failure, total)
import Language.Arbitrary qualified as Arbitrary

import Bench

------ Utilities ------

parse :: Parse a => Text -> a
parse = fromJust . lexParse parser

inspect :: (Show a, Pretty a) => a -> IO ()
inspect x = do
  print x
  putStrLn ""
  print (pretty x)

instance (Pretty e, Pretty a) => Pretty (Either e a) where
  pretty = either pretty pretty

------ Examples -------

{-# NOINLINE benches #-}
benches :: [Named Spec]
benches = Unsafe.unsafePerformIO loadAll

getBench :: Name -> Named Spec
getBench name = Named name . fromJust $ find name benches

instance IsString (Named Spec) where
  fromString = getBench . fromString

instance IsString Spec where
  fromString = (.value) . fromString @(Named Spec)

synth :: Spec -> Maybe (Program Void)
synth spec = case synthesize def spec of
  Success ((_, Finished program) :| _) -> Just program
  _ -> Nothing

runCheck :: Spec -> Either Conflict [Rule]
runCheck = check datatypes

testExtract :: Program Void -> Spec -> IO [Bool]
testExtract program spec = forM spec.examples \example ->
  let
    inputs = map Value example.inputs
    expr = Apps program inputs
  in case normalize expr of
    Value output
      | output == example.output -> return True
      | otherwise -> do
        putStrLn "Test failed"
        print $ "Expected:" <+> pretty example.output
        print $ "Got:" <+> pretty output
        return False
    e -> do
      print $ "Not a value:" <+> pretty e
      return False

pattern PROGRAM :: Program Void -> Solution
pattern PROGRAM p <- Success ((_, Finished p) :| _)

tryOut :: Interpret a => Spec -> a
tryOut spec = case synthesize def spec of
  Success ((_, Finished program) :| _) -> interpret program
  _ -> error "Synthesis failed"
