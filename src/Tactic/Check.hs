module Tactic.Check (rerealize, assert) where

import Control.Carrier.Error.Either
import Control.Carrier.Reader

import Base
import Language.Container.Morphism
import Language.Problem
import Language.Coverage
import Tactic.Core
import Tactic.Extract

-- Recompute realizability
rerealize :: Tactic sig m => m Filling -> m Filling
rerealize cnt = do
  context <- ask
  problem <- ask
  Settings { realizabilityLevel, checkCoverage, reconstructProblem } <- ask
  -- NOTE: not performing realizability breaks the map < foldr relation, so requires a weaker tactic.
  case realizabilityLevel of
    NoRealizability -> cnt
    MonoRealizability -> case monoCheck problem of
      Nothing -> cnt
      Just xs -> throwError . Unrealizable $ MonoConflict xs
    PolyRealizability -> case check context problem of
      Left err -> throwError $ Unrealizable err
      Right rules
        -- NOTE: coverage seems to have a very small overhead, and sometimes leads to a speedup
        -- coverage works mostly for folds, since they can remove input lists, allowing for a change in coverage.
        | checkCoverage, Total <- coverage context problem.signature rules -> cnt >>> extract
        -- NOTE: Reconstruction seems to improve performance slightly by simplifying the resulting constraint.
        | reconstructProblem -> local (reconstruct rules) cnt
        | otherwise -> cnt

assert :: (Tactic sig m) => Example -> m Filling
assert example = local (\problem  -> problem { examples = example : problem.examples }) $ rerealize none
