module Tactic.Filter where

import Base
import Control.Effect.Fresh.Named
import Data.List qualified as List

import Language.Expr
import Language.Problem
import Language.Type

import Tactic.Core
import Tactic.Check
import Tactic.Hole

isFilter :: Eq a => [a] -> [a] -> Bool
isFilter xs ys = List.filter (`elem` ys) xs == ys

filter :: Tactic sig m => Name -> m Filling
filter name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    problem <- ask @Problem
    case (mono, problem.signature.output) of
      (Data "List" [t], Data "List" [u]) -> do
        when (t /= u) $ throwError $ NotApplicable "list types do not match"
        examples <- forM (zip terms problem.examples) \case
          (List inputs, Example scope (List outputs)) -> do
            unless (isFilter inputs outputs) $ throwError $ PropagationError "not a filter"
            return $ List.nub inputs <&> \x ->
              Example (scope ++ [x]) $ Bool $ x `elem` outputs
          _ -> error "Not actually lists."
        x <- freshName "x"
        let
          Signature constraints context _ = problem.signature
          signature =
            Signature constraints (context ++ [Named x t]) (Data "Bool" [])
          subproblem = Problem signature $ concat examples
        local (const subproblem) do
          f <- rerealize hole
          let result = Apps (Var "filter") [Lams [x] f, Var name]
          return result
      _ -> throwError $ NotApplicable "filter only works on lists"

mapFocus :: ([a] -> a -> [a] -> b) -> [a] -> [b]
mapFocus f = go []
  where
    go _ [] = []
    go ys (x:xs) = f ys x xs : go (x:ys) xs

-- Generalized filter whose predicate has access to the rest of the list
filterRest :: Tactic sig m => Name -> m Filling
filterRest name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    problem <- ask @Problem
    case (mono, problem.signature.output) of
      (Data "List" [t], Data "List" [u]) -> do
        when (t /= u) $ throwError $ NotApplicable "list types do not match"
        examples <- forM (zip terms problem.examples) \case
          (List inputs, Example scope (List outputs)) -> do
            -- TODO: check if this is really correct, since this is more general than `isFilter` allows, I think.
            unless (isFilter inputs outputs) $ throwError $ PropagationError "not a filter"
            return $ List.nub inputs & mapFocus \as x bs ->
              Example (scope ++ [x, List (as ++ bs)]) $ Bool $ x `elem` outputs
          _ -> error "Not actually lists."
        x <- freshName "x"
        xs <- freshName "xs"
        let
          Signature constraints context _ = problem.signature
          signature =
            Signature constraints (context ++ [Named x t, Named xs (Data "List" [t])]) (Data "Bool" [])
          subproblem = Problem signature $ concat examples
        local (const subproblem) do
          f <- rerealize hole
          let result = Apps (Var "filterRest") [Lams [x, xs] f, Var name]
          return result
      _ -> throwError $ NotApplicable "filter only works on lists"

-- filter whose predicate has access to the whole input list
filterArg :: Tactic sig m => Name -> m Filling
filterArg name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    problem <- ask @Problem
    case (mono, problem.signature.output) of
      (Data "List" [t], Data "List" [u]) -> do
        when (t /= u) $ throwError $ NotApplicable "list types do not match"
        examples <- forM (zip terms problem.examples) \case
          (List inputs, Example scope (List outputs)) -> do
            -- TODO: check if this is really correct, since this is more general than `isFilter` allows, I think.
            unless (isFilter inputs outputs) $ throwError $ PropagationError "not a filter"
            return $ List.nub inputs <&> \x ->
              Example (scope ++ [x, List inputs]) $ Bool $ x `elem` outputs
          _ -> error "Not actually lists."
        x <- freshName "x"
        xs <- freshName "xs"
        let
          Signature constraints context _ = problem.signature
          signature =
            Signature constraints (context ++ [Named x t, Named xs (Data "List" [t])]) (Data "Bool" [])
          subproblem = Problem signature $ concat examples
        local (const subproblem) do
          f <- rerealize hole
          let result = Apps (Var "filterArg") [Lams [x, xs] f, Var name]
          return result
      _ -> throwError $ NotApplicable "filter only works on lists"

-- NOTE: one way to generalize filter.
-- It would be cool to define filter in terms of partition, but we'd need to first introduce a 'fst' tactic, which has a wildcard on the second field of a tuple.
partition :: Tactic sig m => Name -> m Filling
partition name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    problem <- ask @Problem
    case (mono, problem.signature.output) of
      (Data "List" [t], Product [Data "List" [u], Data "List" [v]]) -> do
        when (t /= u || t /= v) $ throwError $ NotApplicable "list types do not match"
        examples <- forM (zip terms problem.examples) \case
          (List inputs, Example scope (Tuple [List trues, List falses])) -> do
            unless (isFilter inputs trues && isFilter inputs falses) $ throwError $ PropagationError "not a partition"
            return $ List.nub inputs <&> \x ->
              Example (scope ++ [x]) $ Bool $ x `elem` trues
          _ -> error "Not actually lists."
        x <- freshName "x"
        let
          Signature constraints context _ = problem.signature
          signature =
            Signature constraints (context ++ [Named x t]) (Data "Bool" [])
          subproblem = Problem signature $ concat examples
        local (const subproblem) do
          f <- rerealize hole
          let result = Apps (Var "partition") [Lams [x] f, Var name]
          return result
      _ -> throwError $ NotApplicable "span only works on `List a -> (List a, List a)`"

