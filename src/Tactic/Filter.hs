module Tactic.Filter where

import Base
import Control.Effect.Fresh.Named
import Data.List qualified as List

import Language.Expr
import Language.Spec
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
    spec <- ask @Spec
    case (mono, spec.signature.output) of
      (Data "List" [t], Data "List" [u]) -> do
        when (t /= u) $ throwError $ NotApplicable "list types do not match"
        examples <- forM (zip terms spec.examples) \case
          (List inputs, Example scope (List outputs)) -> do
            unless (isFilter inputs outputs) $ throwError $ PropagationError "not a filter"
            return $ List.nub inputs <&> \x ->
              Example (scope ++ [x]) $ Bool $ x `elem` outputs
          _ -> error "Not actually lists."
        x <- freshName "x"
        let
          Signature constraints context _ = spec.signature
          signature =
            Signature constraints (context ++ [Named x t]) (Data "Bool" [])
          subspec = Spec signature $ concat examples
        local (const subspec) do
          f <- rerealize hole
          let result = Apps (Var "filter") [Lams [x] f, Var name]
          return result
      _ -> throwError $ NotApplicable "filter only works on lists"
