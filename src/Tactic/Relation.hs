module Tactic.Relation where

import Base

import Language.Expr
import Language.Problem
import Language.Type

import Tactic.Core
import Tactic.Elim

-- TODO: these should add some value in scope that tells the totality checker
-- that some cases are not possible anymore.

relations :: Tactic sig m => Name -> Name -> m Filling
relations x y = elimOrd x y <| elimEq x y

elimEq :: Tactic sig m => Name -> Name -> m Filling
elimEq name1 name2 = do
  x <- getArg name1
  y <- getArg name2
  problem <- ask @Problem
  case (x, y) of
    (Arg (Free a) xs, Arg (Free b) ys) -> do
      when (a /= b) $ throwError $ NotApplicable "args done't have the same type"
      when (Eq a `notElem` problem.signature.constraints) $
        throwError $ NotApplicable "type has no Eq constraint"
      let bools = Arg (Data "Bool" []) $ Bool <$> zipWith (==) xs ys
      elimArg (Apps (Var "eq") [Var name1, Var name2]) bools
    _ -> throwError $ NotApplicable "args aren't free variables"

elimOrd :: Tactic sig m => Name -> Name -> m Filling
elimOrd name1 name2 = do
  x <- getArg name1
  y <- getArg name2
  problem <- ask @Problem
  case (x, y) of
    (Arg (Free a) xs, Arg (Free b) ys) -> do
      when (a /= b) $ throwError $ NotApplicable "args done't have the same type"
      when (Ord a `notElem` problem.signature.constraints) $
        throwError $ NotApplicable "type has no Ord constraint"
      case (traverse isValue xs, traverse isValue ys) of
        (Just xs', Just ys') -> do
          let ords = Arg (Data "Ordering" []) $ Ordering <$> zipWith compareVal xs' ys'
          elimArg (Apps (Var "cmp") [Var name1, Var name2]) ords
        _ -> error "variables not literals"

    _ -> throwError $ NotApplicable "args aren't free variables"
