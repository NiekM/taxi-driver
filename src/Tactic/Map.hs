module Tactic.Map where

import Base
import Control.Effect.Fresh.Named
import Data.Some

import Language.Expr
import Language.Problem
import Language.Type

import Tactic.Check
import Tactic.Core
import Tactic.Hole

map :: Tactic sig m => Name -> m Filling
map name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    problem <- ask @Problem
    case (mono, problem.signature.output) of
      (Data "List" [t], Data "List" [u]) -> do
        examples <- forM (zip terms problem.examples) \case
          (List inputs, Example scope (List outputs)) -> do
            unless (length inputs == length outputs) $ throwError $ PropagationError "input and output length don't match"
            return $ zipWith (\x y -> Example (scope ++ [x]) y) inputs outputs
          _ -> error "Not actually lists."
        x <- freshName "x"
        let Signature constraints context _ = problem.signature
        let signature = Signature constraints (context ++ [Named x t]) u
        let subproblem = Problem signature $ concat examples
        local (const subproblem) do
          f <- rerealize hole
          let result = Apps (Var "map") [Lams [x] f, Var name]
          return result
      _ -> throwError $ NotApplicable "map only implemented for lists"

mapSome :: Tactic sig m => Name -> m Filling
mapSome name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    problem <- ask @Problem
    case (mono, problem.signature.output) of
      (Data "List" [t], Data "List" [u]) -> do
        examples <- forM (zip terms problem.examples) \case
          (List inputs, Example scope (List outputs)) -> do
            unless (length inputs == length outputs) $ throwError $ PropagationError "input and output length don't match"
            let
              xs = case inputs of
                [] -> error "cannot be"
                (y:ys) -> toExpr _ $ toSome y ys
            return $ zipWith
              (\x y -> Example (scope ++ [x, xs]) y) inputs outputs
          _ -> error "Not actually lists."
        x <- freshName "x"
        xs <- freshName "xs"
        let Signature constraints context _ = problem.signature
        -- TODO: make sure both x and xs are in scope.
        let new = [Named x t, Named xs (Data "Some" [t])]
        let signature = Signature constraints (context ++ new) u
        let subproblem = Problem signature $ concat examples
        local (const subproblem) do
          f <- rerealize hole
          let result = Apps (Var "map") [Lams [x] f, Var name]
          return result
      _ -> throwError $ NotApplicable "mapSome only implemented for lists"


