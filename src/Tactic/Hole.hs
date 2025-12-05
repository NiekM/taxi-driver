module Tactic.Hole (hole) where

import Data.Set qualified as Set

import Control.Carrier.Reader
import Control.Effect.Fresh.Named

import Base
import Language.Expr
import Language.Problem
import Language.Type
import Tactic.Core

import Utils

hole :: Tactic sig m => m Filling
hole = do
  tacticOptions :: TacticOptions <- ask
  foldr @[] (.) id
    [ elimTuples
    , applyWhen tacticOptions.removeDuplicates $ local removeIdenticalInputs
    ] none

removeIdenticalInputs :: Problem -> Problem
removeIdenticalInputs = onArgs \args ->
  Args (nubOn (.value) args.inputs) args.output

-- TODO: ideally this should also peel of constructors of types that only have a single constructor.
elimTuples :: Tactic sig m => m Filling -> m Filling
elimTuples cnt = do
  args <- asks toArgs
  let
    tuples = args.inputs & filter \arg -> case arg.value.mono of
      Product _ -> True
      _ -> False
    components = tuples >>= \(Named name arg) -> peel (Var name) arg
  xs <- zipWithM nominate (Base.repeat "x") components
  let terms = map (vacuous . fst <$>) xs
  let old = map (.name) tuples
  let new = map (snd <$>) xs
  local (hide old) do
    local (addInputs new) do
      lets terms <$> cnt
  where
    peel :: Program Void -> Arg -> [(Program Void, Arg)]
    peel expr arg = case arg.mono of
      Product _ -> concat $ zipWith (\i e -> peel (Prj i expr) e)
        [0..] (projections arg)
      _ -> [(expr, arg)]
