module Language.Container.Morphism where

import Data.List.NonEmpty qualified as NonEmpty
import Data.Map qualified as Map

import Control.Carrier.Reader
import Control.Carrier.Throw.Either

import Base
import Data.Map.Multi (Multi)
import Data.Map.Multi qualified as Multi

import Language.Type
import Language.Expr
import Language.Spec
import Language.Container
import Language.Container.Relation
import Utils

-- TODO: maybe rewrite with some other datatype?
type Origins = Multi Position Position

computeOrigins :: Ord a => Map Position a -> Map Position a -> Origins
computeOrigins p q = Multi.remapping (Multi.fromMap q) (Multi.fromMap p)
  & Multi.filterWithKey \k v -> k.name == v.name

data Pattern = Pattern
  { shapes    :: [Shape]
  , relations :: [Relation]
  } deriving stock (Eq, Ord, Show)

-- A polymorphic input-output example, i.e. an input-output example for
-- container morphisms.
data Rule = Rule
  { input   :: Pattern
  , output  :: Shape
  , origins :: Origins
  } deriving stock (Eq, Ord, Show)

-- It seems that we only need to compute the relation for the inputs, since the
-- output values are a subset (and if they are not, this is already a conflict).
checkExample :: DataContext -> Signature -> Example -> Either Conflict Rule
checkExample dataContext signature example = do
  let types = map (.value) signature.inputs

  let input  = toContainer dataContext (Product types) (Tuple example.inputs)
  let output = toContainer dataContext signature.output example.output

  let
    relations = computeRelations signature.constraints input.elements
    shapes = projections input.shape
    result = Rule
      { input   = Pattern shapes relations
      , output  = output.shape
      , origins = computeOrigins input.elements output.elements
      }

  when (length types /= length example.inputs)
    $ throwError $ ArgumentMismatch types example.inputs
  unless (Multi.consistent result.origins)
    $ throwError $ MagicOutput Spec { signature, examples = [example] }

  return result

-- | Combine multiple examples, checking if there are no conflicts.
combine :: Has (Throw Conflict) sig m => [Rule] -> m [Rule]
combine = traverse merge . NonEmpty.groupAllWith (.input)
  where
    merge :: Has (Throw Conflict) sig m => NonEmpty Rule -> m Rule
    merge rules = case grouped of
      (result :| [])
        | Multi.consistent result.origins -> return result
        | otherwise -> throwError $ PositionConflict (NonEmpty.nub rules)
      _ -> throwError $ ShapeConflict grouped
      where
        grouped = intersect <$> NonEmpty.groupAllWith1 (.output) rules

    intersect :: NonEmpty Rule -> Rule
    intersect rules@(rule :| _) = rule
      { origins = foldl1 Multi.intersection $ fmap (.origins) rules }

data Conflict
  = ArgumentMismatch [Mono] [Value]
  | ShapeConflict (NonEmpty Rule)
  | MagicOutput Spec
  | PositionConflict (NonEmpty Rule)
  | MonoConflict (NonEmpty (NonEmpty Example))
  deriving stock (Eq, Ord, Show)

-- TODO: before checking the realizability w.r.t. parametricity, it might be
-- good to check whether the type is inhabited. Especially in the case were
-- there are no examples, we should still be able to check automatically that
-- e.g. `{x : a} -> b` is not realizable.
check :: DataContext -> Spec -> Either Conflict [Rule]
check dataContext spec =
  combine =<< mapM (checkExample dataContext spec.signature) spec.examples

matchShape :: Shape -> Value -> Maybe (Map Position Value)
matchShape (Tuple xs) (Tuple ys) = Map.unions <$> zipWithM matchShape xs ys
matchShape (Ctr c x) (Ctr d y) | c == d = matchShape x y
matchShape (Lit i) (Lit j) | i == j = Just Map.empty
matchShape (Hole p) x = Just $ Map.singleton p x
matchShape _ _ = Nothing

matchPattern :: Pattern -> [Value] -> Maybe (Map Position Value)
matchPattern patt terms = do
  elements <- Map.unions <$> zipWithM matchShape patt.shapes terms
  guard $ all (checkRelation elements) patt.relations
  return elements

applyRule :: Rule -> [Value] -> Maybe Value
applyRule rule terms = do
  inElements <- matchPattern rule.input terms
  outElements <-
    -- Here, at the call to toMap, we arbitrarily pick one origin, which leads
    -- to a bug...
    Multi.toMap $ Multi.compose (Multi.fromMap inElements) rule.origins
  accept <$> inject outElements rule.output

applyRules :: [Rule] -> [Value] -> Maybe Value
applyRules rules terms = altMap (`applyRule` terms) rules

reconstruct :: [Rule] -> Spec -> Spec
reconstruct rules spec = spec { examples = fromRule <$> rules }
  where
    fromRule rule = fromMaybe (error "err") $
      spec.examples & altMap \example ->
        Example example.inputs <$> applyRule rule example.inputs
