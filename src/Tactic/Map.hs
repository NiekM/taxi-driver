module Tactic.Map where

import Base
import Control.Effect.Fresh.Named

import Language.Expr
import Language.Spec
import Language.Type

import Tactic.Check
import Tactic.Core
import Tactic.Hole

map :: Tactic sig m => Name -> m Filling
map name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    spec <- ask @Spec
    case (mono, spec.signature.output) of
      (Data "List" [t], Data "List" [u]) -> do
        examples <- forM (zip terms spec.examples) \case
          (List inputs, Example scope (List outputs)) -> do
            unless (length inputs == length outputs) $ throwError $ PropagationError "input and output length don't match"
            return $ zipWith (\x y -> Example (scope ++ [x]) y) inputs outputs
          _ -> error "Not actually lists."
        x <- freshName "x"
        let Signature constraints context _ = spec.signature
        let signature = Signature constraints (context ++ [Named x t]) u
        let subspec = Spec signature $ concat examples
        local (const subspec) do
          f <- rerealize hole
          let result = Apps (Var "map") [Lams [x] f, Var name]
          return result
      _ -> throwError $ NotApplicable "map only implemented for lists"
