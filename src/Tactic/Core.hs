module Tactic.Core
  ( Tactic,
    TacticFailure (..),
    module Tactic.Options,
    Filling,
    none,
    assume,
    exact,
    andThen,
    (>>>),
    focus,
    (>>*),
    inOrder,
    repeat,
    replicate,
    orElse,
    (<|),
    firstOf,
    until,
    anywhereBiased,
    anywhereBiased2,
    -- NOTE: Not sure about these
    getArg,
    binds,
  )
where

import Base hiding (repeat, replicate)
import Base qualified
import Control.Effect.Fresh.Named
import Control.Effect.Weight
import Data.List qualified as List
import Language.Container.Morphism
import Language.Expr
import Language.Pretty ()
import Language.Problem
import Language.Type
import Tactic.Options
import Utils

data TacticFailure
  = NotApplicable Text
  | TraceIncomplete
  | PropagationError Text
  | Unrealizable Conflict
  deriving stock (Eq, Ord, Show)

instance Pretty TacticFailure where
  pretty = \case
    NotApplicable t -> "Not Applicable:" <+> pretty t
    TraceIncomplete -> "Trace Incomplete"
    PropagationError t -> "Propagation Failed:" <+> pretty t
    Unrealizable conflict -> pretty conflict

type Tactic sig m =
  ( Has (Reader DataContext) sig m
  , Has (Reader TacticOptions) sig m
  , Has (Reader Problem) sig m
  , Has Fresh sig m
  , Has Weight sig m
  , Has (Error TacticFailure) sig m
  )

type Filling = Program Problem

none :: (Tactic sig m) => m Filling
none = Hole <$> ask

assume :: (Tactic sig m) => Name -> m Filling
assume name = do
  arg <- getArg name
  out <- asks outputArg
  when (arg /= out) $ throwError $ NotApplicable "argument doesn't match spec"
  return $ Var name

exact :: (Tactic sig m) => Program Void -> Mono -> m Filling
exact expr t = do
  problem <- ask
  out <- asks outputArg
  when (t /= out.mono) $ throwError $ NotApplicable "expression has incorrect typ"
  case evaluate expr problem of
    Nothing -> throwError $ NotApplicable "expression does not evaluate to a Value"
    Just result | result == (outputArg problem).terms -> return $ vacuous expr
    _ -> throwError $ NotApplicable "expression does not match output"

infixl 3 >>>

andThen, (>>>) :: (Tactic sig m) => m Filling -> m Filling -> m Filling
andThen f g = do
  filling <- f
  join <$> forM filling \p -> local (const p) g
(>>>) = andThen

focus :: (Tactic sig m) => Nat -> m Filling -> m Filling -> m Filling
focus n f g = f >>* (Base.replicate (fromIntegral n) none ++ [g])

(>>*) :: (Tactic sig m) => m Filling -> [m Filling] -> m Filling
(>>*) f gs = do
  filling <- f
  let numbered = enumerate filling
  join <$> forM numbered \(n, p) ->
    local (const p) case gs List.!? (fromIntegral n) of
      Nothing -> none
      Just g -> g

inOrder :: (Tactic sig m) => [m Filling] -> m Filling
inOrder = foldr (>>>) none

replicate :: (Tactic sig m) => Nat -> m Filling -> m Filling
replicate 0 _ = none
replicate n tactic = tactic >>> replicate (n - 1) tactic

repeat :: (Tactic sig m) => m Filling -> m Filling
repeat tactic = tactic >>> repeat tactic

infixl 2 <|

orElse, (<|) :: (Tactic sig m) => m a -> m a -> m a
orElse t u = catchError @TacticFailure t $ const u
(<|) = orElse

firstOf :: (Tactic sig m) => NonEmpty (m a) -> m a
firstOf = foldr1 orElse

until :: (Tactic sig m, Has (Catch TacticFailure) sig m) => m Filling -> m Filling -> m Filling
until t u = t <| u >>> until t u

-- | Apply a tactic to the first variable in scope that succeeds.
anywhereBiased :: (Tactic sig m) => (Name -> m a) -> m a
anywhereBiased tactic = do
  vars <- asks variables
  case vars of
    [] -> throwError $ NotApplicable "no variable in scope"
    x : xs -> firstOf $ fmap tactic (x :| xs)

-- | Apply a tactic to the first pair of variables in scope that succeeds.
anywhereBiased2 :: (Tactic sig m) => (Name -> Name -> m a) -> m a
anywhereBiased2 tactic = do
  vars <- asks variables
  let pairs = [(x, y) | x <- vars, y <- vars, x < y]
  case pairs of
    [] -> throwError $ NotApplicable "no two variables in scope"
    x : xs -> firstOf $ fmap (uncurry tactic) (x :| xs)

getArg :: (Tactic sig m) => Name -> m Arg
getArg name = do
  inputs <- asks inputArgs
  case find name inputs of
    Nothing -> throwError $ NotApplicable $ "unknown name " <> name.getName
    Just arg -> return arg

binds :: (Tactic sig m) => [Named Arg] -> m Filling -> m Filling
binds args body = do
  renamed <- forM args \(Named name arg) -> nominate name arg
  local (addInputs renamed) do
    let vars = map (.name) renamed
    Lams vars <$> body
