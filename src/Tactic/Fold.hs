{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Tactic.Fold where

import Base hiding (fold)
import Control.Effect.Fresh.Named

import Language.Expr
import Language.Spec
import Language.Type
import Language.Container
import Language.Container.Morphism

import Tactic.Check
import Tactic.Core
import Tactic.Elim
import Tactic.Hole

getBaseFunctor :: Tactic sig m => Mono -> m (Name, [Mono])
getBaseFunctor = \case
  Data d ts -> do
    let baseFunctor = d <> "F"
    ds <- ask @DataContext
    case find baseFunctor ds.datatypes of
      Nothing -> throwError $ NotApplicable "cannot unroll nonrecursive datatype"
      _ -> return ()
    return (baseFunctor, ts)
  _ -> throwError $ NotApplicable "cannot unroll nondatatype"

unroll :: Tactic sig m => Mono -> Term Void -> m (Term (Term Void))
unroll mono term = do
  (baseFunctor, types) <- getBaseFunctor mono
  ctx <- ask
  let matched = poly ctx (Data baseFunctor (types ++ [Free "r"])) term
  return $ matched >>= \case
    ("r", x) -> return x
    (_, other) -> absurd <$> other

fold :: Tactic sig m => Name -> m Filling
fold name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    spec <- ask @Spec
    ctx <- ask

    rules <- either (throwError . Unrealizable) return $ check ctx Spec
      { signature = spec.signature
        { inputs = Named name mono : spec.signature.inputs }
      , examples = zip terms spec.examples <&>
        \(i, Example is o) -> Example (i:is) o
      }

    let recurse = applyRules rules

    unrolled <- forM terms $ unroll mono

    examples <- forM (zip unrolled spec.examples)
      \(argument, Example inputs output) -> do
        fixed <- join <$> forM argument \x ->
          maybe (throwError TraceIncomplete) pure $ recurse (x:inputs)
        return $ Example (inputs ++ [fixed]) output

    (baseFunctor, types) <- getBaseFunctor mono

    r <- freshName "r"
    f <- local (const $ Spec spec.signature
      { inputs = spec.signature.inputs ++
        [ Named r $ Data baseFunctor (types ++ [spec.signature.output]) ]
      } examples) $ elim r >>> rerealize hole

    let result = Apps (Var "cata") [Lams [r] f, Var name]
    return result

para :: Tactic sig m => Name -> m Filling
para name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    spec <- ask @Spec
    ctx <- ask

    rules <- either (throwError . Unrealizable) return $ check ctx Spec
      { signature = spec.signature
        { inputs = Named name mono : spec.signature.inputs }
      , examples = zip terms spec.examples <&>
        \(i, Example is o) -> Example (i:is) o
      }

    let recurse = applyRules rules

    unrolled <- forM terms $ unroll mono

    examples <- forM (zip unrolled spec.examples)
      \(argument, Example inputs output) -> do
        fixed <- join <$> forM argument \x ->
          maybe (throwError TraceIncomplete) (pure . Tuple . (:[x])) $ recurse (x:inputs)
        return $ Example (inputs ++ [fixed]) output

    (baseFunctor, types) <- getBaseFunctor mono

    r <- freshName "r"
    f <- local (const $ Spec spec.signature
      { inputs = spec.signature.inputs ++
        [ Named r $ Data baseFunctor (types ++
          [Product [spec.signature.output, mono]])
        ]
      } examples) $ elim r >>> rerealize hole

    let result = Apps (Var "para") [Lams [r] f, Var name]

    return result

cata :: Tactic sig m => Name -> m Filling
cata name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    spec <- ask @Spec
    ctx <- ask

    rules <- either (throwError . Unrealizable) return $ check ctx Spec
      { signature = spec.signature
        { inputs = Named name mono : spec.signature.inputs }
      , examples = zip terms spec.examples <&>
        \(i, Example is o) -> Example (i:is) o
      }

    let recurse = applyRules rules

    unrolled <- forM terms $ unroll mono

    examples <- forM (zip unrolled spec.examples)
      \(argument, Example inputs output) -> do
        fixed <- join <$> forM argument \x ->
          maybe (throwError TraceIncomplete) pure $ recurse (x:inputs)
        return $ Example (inputs ++ [fixed]) output

    (baseFunctor, types) <- getBaseFunctor mono

    r <- freshName "r"
    f <- local (const $ Spec spec.signature
      { inputs = spec.signature.inputs ++
        [ Named r $ Data baseFunctor (types ++ [spec.signature.output]) ]
      } examples) $ rerealize hole

    let result = Apps (Var "cata") [Lams [r] f, Var name]
    return result
