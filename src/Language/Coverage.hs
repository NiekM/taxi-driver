module Language.Coverage (Coverage(..), coverage) where

import Control.Carrier.State.Lazy
import Data.List qualified as List
import Data.Set qualified as Set
import Data.Map.Strict qualified as Map

import Base
import Language.Expr
import Language.Type
import Language.Container
import Language.Container.Morphism
import Language.Container.Relation

-- TODO: we might be able to speed up coverage generation using cashing.
-- However, currently the overhead is not very significant.

coveringShapes :: DataContext -> Mono -> Maybe [Term Name]
coveringShapes ctx = go []
  where
    -- We keep track of datatype names to recognize recursion.
    go :: [Name] -> Mono -> Maybe [Term Name]
    go recs = \case
      -- Holes remember their type, so that we can fill in the positions later.
      Free a -> return [Hole a]
      Product ts -> do
        xss <- traverse (go recs) ts
        return $ Tuple <$> sequence xss
      Data d ts
        | d `elem` recs -> Nothing
        | otherwise ->
          concat <$> forM (getConstructors d ts ctx) \(Named c t) -> do
            xs <- go (d : recs) t
            return $ Ctr c <$> xs
      Base Int -> Nothing

-- TODO: rename to avoid confusion
anywhere :: (a -> b -> [b]) -> (a -> b) -> a -> [b] -> [[b]]
anywhere _ e x [] = [[e x]]
anywhere f e x (y:ys) = (f x y ++ ys) : map (y:) (anywhere f e x ys)

prependAnywhere :: a -> [[a]] -> [[[a]]]
prependAnywhere = anywhere (\x xs -> [x:xs]) return

-- | All possible ways to divide a list into non-empty sublists.
subs :: [a] -> [[[a]]]
subs = List.foldr (concatMap . prependAnywhere) [[]]

insertAnywhere :: a -> [a] -> [[a]]
insertAnywhere = anywhere (\x y -> [x, y]) id

orderings :: [a] -> [[a]]
orderings = List.foldr (concatMap . insertAnywhere) [[]]

coveringRelations :: [Position] -> Constraint -> [Relation]
coveringRelations ps = \case
  Eq a ->
    let qs = filter (\pos -> pos.name == a) ps
    in RelEq . Set.fromList . map Set.fromList <$> subs qs
  Ord a ->
    let qs = filter (\pos -> pos.name == a) ps
    in RelOrd . map Set.fromList <$> concatMap orderings (subs qs)

toShape :: Term Name -> Shape
toShape e = run $ evalState @(Map Name Nat) mempty do
  forM e \v -> do
    m <- get
    let n = fromMaybe 0 $ Map.lookup v m
    modify $ Map.insert v (n + 1)
    return $ Named v n

-- Computes all shapes and relations required for coverage (if possible)
coveringPatterns :: DataContext -> [Constraint] -> [Mono] -> Maybe [Pattern]
coveringPatterns ctx constraints context = do
  shapes <- map toShape <$> coveringShapes ctx (Product context)
  concat <$> forM shapes \shape -> do
    let
      inputs = projections shape
      positions = holes shape
      relations = traverse (coveringRelations positions) constraints
    return $ Pattern inputs <$> relations

expectedCoverage :: DataContext -> Signature -> Maybe (Set Pattern)
expectedCoverage ctx signature = Set.fromList <$> coveringPatterns ctx
  signature.constraints
  (map (.value) signature.inputs)

ruleCoverage :: [Rule] -> Set Pattern
ruleCoverage = Set.fromList <$> map (.input)

data Coverage = Total | Partial | Missing (Set Pattern)
  deriving (Eq, Ord, Show)

-- TODO: what kind of coverage do we need? how do we check shape coverage
-- nicely? maybe translate to Map Shape Relation? might be better in general as
-- coverage result. even if shapes are missing, we still want to know which
-- relations are missing for other shapes. if a shape is missing, do we also
-- still want to return which relations go with that shape? if there are too
-- many shapes to cover, because of e.g. a list as input, do we still want to
-- have relation coverage? or subpattern coverage, e.g. if it's a list booleans,
-- do we still want coverage checking for a pattern such as [True], letting us
-- know that we are missing [False]?
coverage :: DataContext -> Signature -> [Rule] -> Coverage
coverage dataContext signature examples = case expectedCoverage dataContext signature of
  Nothing -> Partial
  Just expected ->
    let
      covered = ruleCoverage examples
      missing = expected Set.\\ covered
      -- shapes = Set.map (.shapes) expected Set.\\ Set.map (.shapes) covered
    in if null missing then Total else Missing missing
