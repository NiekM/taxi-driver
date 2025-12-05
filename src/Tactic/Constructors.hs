{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Tactic.Constructors where

import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty

import Base
import Language.Expr
import Language.Spec
import Language.Type
import Tactic.Core
import Tactic.Hole

constructors :: Tactic sig m => m Filling
constructors = introCtr <| introTuple

introTuple :: Tactic sig m => m Filling
introTuple = do
  spec <- ask @Spec
  case spec.signature.output of
    Product _ ->
      tuple <$> forM (projections spec) \p ->
        local (const p) hole
    _ -> throwError $ NotApplicable "goal is not a tuple"

introCtr :: Tactic sig m => m Filling
introCtr = do
  spec <- ask @Spec
  case spec.signature.output of
    Data d ts -> do
      cs <- asks $ getConstructors d ts
      -- TODO: getConstructor that returns the fields of one specific ctr
      exs <- forM spec.examples \example -> case example.output of
        Ctr c e -> (c,) <$> forM (projections e) \x ->
          return (example { output = x } :: Example)
        _ -> throwError $ NotApplicable "output not a constructor"
      case NonEmpty.groupAllWith fst exs of
        [] -> throwError $ NotApplicable "no examples"
        (_:_:_) -> throwError $ NotApplicable "not all examples agree"
        [xs] -> do
          let c = fst $ NonEmpty.head xs
          let exampless = List.transpose $ snd <$> NonEmpty.toList xs
          case find c cs of
            Nothing -> error "unknown constructor"
            Just ct -> do
              let goals = projections ct
              es <- forM (zip exampless goals) \(examples, output) -> do
                let signature = spec.signature { output } :: Signature
                local (const Spec { signature, examples }) hole
              return . Ctr c $ tuple es
    _ -> throwError $ NotApplicable "goal is not a datatype"
