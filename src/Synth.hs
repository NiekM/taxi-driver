{-# OPTIONS_GHC -Wno-ambiguous-fields #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE DeriveAnyClass #-}

module Synth
  ( synthesize
  , synthesizeAll
  , Solution(..)
  , SynthFailure(..)
  , Extract(..)
  , SynthOptions(..)
  , Synth
  , SynthC
  , step
  , auto
  , runTactic
  , softConditional
  , eliminators
  , staged
  , withPara
  ) where

import Control.Effect.Fresh.Named
import Control.Effect.Search
import Control.Carrier.Error.Either
import Control.Carrier.Reader

import Control.Monad.Search

import Base hiding (repeat, replicate)
import Language.Type
import Language.Expr
import Language.Spec

import Tactic
import Tactic.Combinators
import Tactic.Map qualified as Tactic
import Tactic.Filter qualified as Tactic
import Tactic.Fold qualified as Tactic

import Language.Prelude
import Language.Pretty
import Data.List qualified as List

import Utils
import Data.Functor.Identity (Identity)

data SynthOptions = SynthOptions
  { tactic :: SynthC Filling
  , fuel :: Maybe Nat
  , solutions :: Maybe Nat
  , tacticOptions :: TacticOptions
  , context :: DataContext
  }

instance Default SynthOptions where
  def = SynthOptions
    { tactic = auto
    , fuel = Nothing
    , solutions = Just 1
    , tacticOptions = def
    , context = datatypes
    }

data SynthFailure
  = Exhausted -- out of programs
  | Depleted -- out of fuel
  deriving stock (Eq, Ord, Show)

instance Pretty SynthFailure where
  pretty = \case
    Exhausted -> "Exhausted"
    Depleted -> "Depleted"

data Extract
  = Finished (Program Void)
  | Unfinished Filling
  deriving stock (Eq, Ord, Show)

instance Pretty Extract where
  pretty = \case
    Finished program -> pretty program
    Unfinished filling -> pretty . Split $ withNames "_" filling

data Solution
  = Success (NonEmpty (Nat, Extract))
  | Failure SynthFailure
  deriving stock (Eq, Ord, Show)

instance Pretty Solution where
  pretty = \case
    Success ((_, extr) :| []) -> pretty extr
    Success extracts -> pretty . toList $ fmap snd extracts
    Failure failure -> pretty failure

takeWhileJust :: [Maybe a] -> [a]
takeWhileJust = foldr (maybe (const []) (:)) []

synthesizeAll :: SynthOptions -> Spec -> [(Nat, Either TacticFailure Extract)]
synthesizeAll args spec = runSearch searchSpace & mapMaybe
  \(Sum weight, filling) -> (weight,) . fmap toExtract <$> filling
  where
    toExtract :: Filling -> Extract
    toExtract filling =
      let normalized = normalize filling
      in case vacate normalized of
        Nothing -> Unfinished normalized
        Just program -> Finished program

    searchSpace :: Search (Sum Nat) (Maybe (Either TacticFailure Filling))
    searchSpace = maybe (fmap Just) limit args.fuel
      . evalFresh
      . runError
      . runReader args.context
      . runReader args.tacticOptions
      . runReader spec
      $ Lams (variables spec) <$> (rerealize hole >>> args.tactic)

synthesize :: SynthOptions -> Spec -> Solution
synthesize args spec = case dropFailures $ runSearch searchSpace of
  [] -> Failure Exhausted
  -- TODO: when we add a fuel limit, it says depleted even if it should be
  -- exhausted. How do we distinguish between them?
  xs ->
    let take = maybe id List.genericTake args.solutions
    in case take . takeWhileJust $ map sequence xs of
    [] -> Failure Depleted
    (y:ys) -> Success $ (y :| ys) <&> \(Sum weight, filling) ->
      (weight, toExtract filling)
  where
    dropFailures :: [(Sum Nat, Maybe (Either a b))] -> [(Sum Nat, Maybe b)]
    dropFailures = mapMaybe $ traverse . traverse $ either (const Nothing) (Just)

    toExtract :: Filling -> Extract
    toExtract filling =
      let normalized = normalize filling
      in case vacate normalized of
        Nothing -> Unfinished normalized
        Just program -> Finished program

    searchSpace :: Search (Sum Nat) (Maybe (Either TacticFailure Filling))
    searchSpace = maybe (fmap Just) limit args.fuel
      . evalFresh
      . runError
      . runReader args.context
      . runReader args.tacticOptions
      . runReader spec
      $ Lams (variables spec) <$> (rerealize hole >>> args.tactic)

type Synth sig m = (Tactic sig m, Has Choose sig m)

-- TODO: can we generate some interactive search thing? Perhaps just an IO monad
-- where you select where to proceed and backtrack?
-- Perhaps use Gloss to render nodes of a tree, where each node shows one
-- refinement. Clicking on refinements explores them (if realizable) and perhaps
-- outputs the current state to the console? Or perhaps a next button that
-- explores the next node (based on its weight).

type TacticC m = ReaderC Spec (ReaderC TacticOptions (ReaderC DataContext (ErrorC TacticFailure (FreshC m))))

type SynthC = TacticC (Search (Sum Nat))

runTactic :: TacticOptions -> DataContext -> Spec -> TacticC (IgnoreC Identity) Filling -> Either TacticFailure Filling
runTactic tacticOptions context spec tactic = do
  let vars = variables spec
  run . ignoreWeight . evalFresh . runError . runReader context . runReader tacticOptions . runReader spec $ Lams vars <$> tactic

-- * Larger tactic groups

eliminators :: Synth sig m => Name -> m Filling
eliminators x = do
  TacticOptions { conditionalBranch } <- ask
  if conditionalBranch
    then Tactic.map x <|  Tactic.filter x <|  (Tactic.fold x <|  (weigh 3 >> elim x))
    else Tactic.map x <|> Tactic.filter x <|> (Tactic.fold x <|> (weigh 3 >> elim x))

-- | The function foo tries to apply tactic t. If it fails, u is applied. If it succeeds, t is applied, but u is still possible, just with increased weight.
softConditional :: Synth sig m => Nat -> m Filling -> m Filling -> m Filling
softConditional n t u = catchError @TacticFailure (do
  x <- t
  pure x <|> (weigh n >> u)) $ const u

step :: Synth sig m => m Filling
step = anywhereBiased assume <| anyOf
  [ weigh 3 >> anywhere eliminators
  -- BUG: currently we can keep applying the same elimEq/elimOrd on the same variables...
  , anywhere2 relations
  , constructors
  ]

auto :: Synth sig m => m Filling
auto = repeat (weigh 1 >> step)

simple :: Synth sig m => m Filling
simple = (anywhereBiased assume <| constructors) <|> (weigh 2 >> anywhere2 relations)

complex :: Synth sig m => Name -> m Filling
complex x = ((Tactic.map x <| Tactic.filter x <| Tactic.fold x) <|> elim x) <| none

-- I thought this might synthesize group, but it still overfits.
-- This is because none of the examples have more than 2 times the same value after another.
staged :: Synth sig m => m Filling
staged = replicate 3 (anywhere complex) >>> repeat simple

-- For synthesizing e.g. insert
--
-- > Success ((_, Finished p) :| _) = synthesize def { tactic = withPara } "insert"
-- > myInsert :: Int -> [Int] -> [Int]; myInsert x xs = interpret $ Apps p [Value (toExpr x), Value (toExpr xs)]
-- > quickCheck \x (Sorted xs) -> myInsert x xs == List.insert x xs
--   +++ OK, passed 100 tests.
--
withPara :: Synth sig m => m Filling
withPara = repeat (weigh 1 >> paraStep)
  where
    paraStep = anywhereBiased assume <| anyOf
      [ weigh 3 >> anywhere \x -> eliminators x <|> Tactic.para x
      , anywhere2 relations
      , constructors
      ]

-- TODO: simulating interactive synthesis with quickCheck:
-- 1. start with no examples
-- 2. synthesize, quickCheck, shrink the incorrect inputs
-- 3. add correct input-output to examples, repeat (from 2)

-- ordNub can be defined in terms of para
-- > Success ((_, Finished p) :|_) = synthesize def { tactic = Tactic.fold "xs" >>> Tactic.para "x2" >>> Tactic.anywhereBiased2 elimOrd >>> auto } "ordNub"
-- > quickCheck \xs -> List.nub (List.sort xs) == interpret @([Nat] -> [Nat]) p xs
-- +++ OK, passed 100 tests.
--
-- same for sort!
-- > Success ((_, Finished p) :|_) = synthesize def { tactic = Tactic.fold "xs" >>> Tactic.para "x2" >>> Tactic.anywhereBiased2 elimOrd >>> auto } "sort"
-- > quickCheck \xs -> List.sort xs == interpret @([Nat] -> [Nat]) p xs
-- +++ OK, passed 100 tests.
--

-- Very slow, but succeeds
-- > Success ((_,Finished p):|_) = synthesize def { tactic = Tactic.fold "xs" >>> Tactic.elim "x2" >>* [none, rerealize hole] >>> Tactic.elim "x5" >>* [anywhereBiased2 elimEq] >>> auto } "group"
-- > quickCheck \xs -> interpret @([Nat] -> [[Nat]]) p xs == List.group xs
-- +++ OK, passed 100 tests

-- encode (i.o. group)
-- $ synthesize def { tactic = Tactic.fold "xs" >>> Tactic.elim "x2" >>* [none, rerealize hole] >>> anywhereBiased2 elimEq >>> introCtr >>> auto} "encode"

-- Paramorphisms:
--
-- > PROGRAM p = synthesize def { tactic = anywhereBiased Tactic.para >>> auto } "insert"
-- > quickCheck \x (Sorted xs) -> interpret @(Nat -> [Nat] -> [Nat]) p x xs == List.insert x xs
-- +++ OK, passed 100 tests.
--
-- > PROGRAM p = synthesize def { tactic = anywhereBiased Tactic.para >>> auto } "sorted"
-- > quickCheck \xs -> interpret @([Nat] -> Bool) p xs == (xs == List.sort xs)
-- +++ OK, passed 100 tests.
--
-- > PROGRAM p = synthesize def { tactic = anywhereBiased Tactic.fold >>> anywhereBiased Tactic.para >>> auto } "sort"
-- > quickCheck \xs -> interpret @([Nat] -> [Nat]) p xs == List.sort xs
-- +++ OK, passed 100 tests.
--
-- > PROGRAM p = synthesize def { tactic = anywhereBiased Tactic.fold >>> anywhereBiased Tactic.para >>> auto } "ordNub"
-- > quickCheck \xs -> interpret @([Nat] -> [Nat]) p xs == List.nub (List.sort xs)
-- +++ OK, passed 100 tests.
