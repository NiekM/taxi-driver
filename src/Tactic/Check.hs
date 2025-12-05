module Tactic.Check (rerealize, assert) where

import Control.Carrier.Error.Either
import Control.Carrier.Reader

import Base
import Language.Container.Morphism
import Language.Spec
import Language.Coverage
import Tactic.Core
import Tactic.Extract

-- Recompute realizability
rerealize :: Tactic sig m => m Filling -> m Filling
rerealize cnt = do
  context <- ask
  spec <- ask
  TacticOptions { realizabilityLevel, checkCoverage, reconstructSpec } <- ask
  -- NOTE: not performing realizability breaks the map < foldr relation, so requires a weaker tactic.
  case realizabilityLevel of
    NoRealizability -> cnt
    MonoRealizability -> case monoCheck spec of
      Nothing -> cnt
      Just xs -> throwError . Unrealizable $ MonoConflict xs
    PolyRealizability -> case check context spec of
      Left err -> throwError $ Unrealizable err
      Right rules
        -- NOTE: coverage seems to have a very small overhead, and sometimes leads to a speedup
        -- coverage works mostly for folds, since they can remove input lists, allowing for a change in coverage.
        | checkCoverage, Total <- coverage context spec.signature rules -> cnt >>> extract
        -- NOTE: Reconstruction seems to improve performance slightly by simplifying the resulting constraint.
        | reconstructSpec -> local (reconstruct rules) cnt
        | otherwise -> cnt

assert :: (Tactic sig m) => Example -> m Filling
assert example = local (\spec  -> spec { examples = example : spec.examples }) $ rerealize none
