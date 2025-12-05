module Tactic.Combinators where

import Control.Effect.Choose

import Base hiding (replicate, repeat, (<|>))
import Language.Spec
import Tactic.Core

anyOf :: (Tactic sig m, Has Choose sig m) => [m a] -> m a
anyOf [] = throwError $ NotApplicable "out of options"
anyOf xs = foldr1 (<|>) xs

anywhere :: (Tactic sig m, Has Choose sig m) => (Name -> m a) -> m a
anywhere tactic = tactic =<< anyOf . map pure =<< asks variables

anywhere2 :: (Tactic sig m, Has Choose sig m) => (Name -> Name -> m a) -> m a
anywhere2 tactic = do
  vars <- asks variables
  x <- anyOf $ map pure vars
  y <- anyOf $ map pure vars
  unless (x < y) $ throwError $ NotApplicable "require separate variables"
  tactic x y
