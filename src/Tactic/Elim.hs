module Tactic.Elim where

import Data.Map qualified as Map

import Control.Carrier.Reader

import Base
import Language.Expr
import Language.Problem
import Language.Type
import Tactic.Core
import Tactic.Hole

elimArg :: Tactic sig m => Program Void -> Arg -> m Filling
elimArg expr arg = do
  ctx <- ask @DataContext
  problem <- ask @Problem
  case split ctx arg problem of
    Left e -> throwError $ NotApplicable $ "elim: " <> e
    Right m -> do
      arms <- forM m \(a, p) -> local (const p) $ binds [Named "x" a] hole
      return $ App (Elim $ Map.assocs arms) (vacuous expr)

elim :: Tactic sig m => Name -> m Filling
elim name = do
  arg <- getArg name
  local (hide [name]) $ elimArg (Var name) arg
