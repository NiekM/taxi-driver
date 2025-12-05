{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE TypeAbstractions #-}
module Language.Expr
  ( Expr
    ( ..
    , Value
    , Unit
    , Apps
    , Lams
    , Case, If
    , Bool
    , Ordering
    , Nil, Cons, List
    , Zero, Succ, Nat
    , Tree, TangoLL, TangoLN
    )
  , Lit(..)
  , Program
  , Term
  , Value, isValue
  , holes
  , accept
  , freeVars
  , normalize
  , asProgram
  , tuple
  , lets
  , compareVal
  , ToExpr(..)
  , FromExpr(..)
  , ToValue, toValue
  , FromValue, fromValue
  , Interpret(..)
  , Execute(..)
  ) where

import GHC.Generics hiding (Constructor)
import GHC.TypeLits (KnownSymbol, symbolVal)

import Data.List qualified as List
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Foldable

import Data.Proxy

import Data.Tango.List.List as LL
import Data.Tango.List.Nat  as LN
import Data.Tree.Binary

import Unsafe.Coerce qualified as Unsafe

import Base

import Test.QuickCheck (SortedList(..))

newtype Lit = MkInt Int
  deriving stock (Eq, Ord, Show)

data Expr (l :: Bool) h where
  -- Constructions
  Tuple :: [Expr l h] -> Expr l h
  -- TODO: use natural numbers for constructors to describe the ordering non-lexicographically
  Ctr :: Name -> Expr l h -> Expr l h
  Lit :: Lit -> Expr l h
  -- Lambda expressions
  Var :: Name -> Program h
  Lam :: Name -> Program h -> Program h
  App :: Program h -> Program h -> Program h
  -- Deconstructions
  Prj :: Nat -> Program h -> Program h
  Elim :: [(Name, Program h)] -> Program h
  -- Holes
  Hole :: h -> Expr l h

-- TODO: The derived Ord instance uses comparison of Text to compare
-- constructors, but this messes with the ordering of examples. Perhaps a
-- better solution would be to just use a natural number internally for
-- constructors and only retrieving the constructor name during pretty
-- printing.
deriving stock instance Eq   h => Eq   (Expr l h)
deriving stock instance Ord  h => Ord  (Expr l h)
deriving stock instance Show h => Show (Expr l h)

deriving stock instance Functor     (Expr l)
deriving stock instance Foldable    (Expr l)
deriving stock instance Traversable (Expr l)

type Program = Expr True
type Term    = Expr False
type Value   = Term Void

instance Applicative (Expr l) where
  pure :: a -> Expr l a
  pure = Hole

  liftA2 :: (a -> b -> c) -> Expr l a -> Expr l b -> Expr l c
  liftA2 f x y = x >>= \a -> y >>= \b -> pure $ f a b

instance Monad (Expr l) where
  (>>=) :: Expr l a -> (a -> Expr l b) -> Expr l b
  x >>= f = accept $ fmap f x

-- Accept the hole fillings (i.e. join)
accept :: Expr l (Expr l h) -> Expr l h
accept = \case
  Tuple xs -> Tuple (map accept xs)
  Ctr c x -> Ctr c (accept x)
  Lit l -> Lit l
  Var v -> Var v
  Lam v x -> Lam v (accept x)
  App f x -> App (accept f) (accept x)
  Prj i x -> Prj i (accept x)
  Elim xs -> Elim (map (fmap accept) xs)
  Hole e -> e

instance Project (Expr l h) where
  projections = \case
    Tuple xs -> xs
    x -> [x]

holes :: Expr l h -> [h]
holes = toList

freeVars :: Program h -> Set Name
freeVars = \case
  Tuple xs -> foldMap freeVars xs
  Ctr _ x -> freeVars x
  Lit _ -> Set.empty
  Var v -> Set.singleton v
  Lam v x -> Set.filter (/= v) $ freeVars x
  App f x -> freeVars f <> freeVars x
  Prj _ x -> freeVars x
  Elim xs -> foldMap (freeVars . snd) xs
  Hole _ -> Set.empty

tuple :: [Expr l h] -> Expr l h
tuple [x] = x
tuple xs = Tuple xs

normalize :: Expr l h -> Expr l h
normalize = norm mempty

foldNat :: Nat -> (a -> a) -> a -> a
foldNat 0 _ e = e
foldNat n f e = f (foldNat (n - 1) f e)

paraNat :: ((Nat, b) -> b) -> b -> Nat -> b
paraNat _ e 0 = e
paraNat g e n = g (n - 1, paraNat g e (n - 1))

paraList :: (a -> ([a], b) -> b) -> b -> [a] -> b
paraList _ e [] = e
paraList g e (y:ys) = g y (ys, paraList g e ys)

-- TODO: define comparison for other values (not using lexicographical ordering of constructors)
compareVal :: Value -> Value -> Ordering
compareVal (Lit i) (Lit j) = compare i j
compareVal (Nat n) (Nat m) = compare n m
compareVal _ _ = error "comparison between non-literals undefined"

norm :: Map Name (Expr l h) -> Expr l h -> Expr l h
norm @_ @h ctx = \case
  Tuple xs -> Tuple $ map (norm ctx) xs
  Ctr c x -> Ctr c $ norm ctx x
  Lit i -> Lit i
  Var v -> case Map.lookup v ctx of
    Just x -> x
    Nothing -> Var v
  Lam v x -> case norm ctx x of
    App f (Var z) | v == z, Set.notMember z (freeVars f) -> f
    y -> Lam v y
  App f x -> case App (norm ctx f) (norm ctx x) of
    App (Lam v e) y -> norm (Map.insert v y ctx) e
    Case (Ctr c e) xs -> case List.lookup c xs of
      Nothing -> error $ "Unknown constructor " <> show c
      Just r -> norm ctx $ App r (norm ctx e)
    Apps (Var "cata") [alg, arg@Ctr{}] -> norm ctx $ appCata alg arg
    Apps (Var "para") [alg, arg@Ctr{}] -> norm ctx $ appPara alg arg
    Apps (Var "map") [g, List xs] -> List $ map (norm ctx . App g) xs
    Apps (Var "filter") [p, List xs] -> List $
      filter (fromMaybe False . fromExpr . norm ctx . App p) xs
    Apps (Var "tango") [List xs, List ys] -> TangoLL $ LL.tango xs ys
    Apps (Var "tango") [List xs, Nat n] -> TangoLN $ LN.tango xs n
    Apps (Var "eq" ) [Value a, Value b] -> Bool (a == b)
    Apps (Var "cmp") [Value a, Value b] -> Ordering (compareVal a b)
    e -> e
  Prj i x -> case norm ctx x of
    Tuple xs -> norm ctx $ xs List.!! fromIntegral i
    y -> Prj i y
  Elim xs -> Elim $ map (norm ctx <$>) xs
  Hole h -> Hole h

  where
    appCata :: Program h -> Program h -> Program h
    appCata alg = \case
      List xs -> foldr (\y r -> App alg $ Cons y r) (App alg Nil) xs
      Tree  t -> foldTree (\l y r -> App alg $ Ctr "Node" $ Tuple [l, y, r]) (App alg . Ctr "Leaf") t
      Nat   n -> foldNat n (App alg . Ctr "Succ") (App alg $ Nat 0)
      TangoLL t -> t & LL.foldTango \case
        NNF -> App alg $ Ctr "NN" Unit
        CNF x xs -> App alg $ Ctr "CN" $ Tuple [x, List xs]
        NCF y ys -> App alg $ Ctr "NC" $ Tuple [y, List ys]
        CCF x y xys -> App alg $ Ctr "CC" $ Tuple [x, y, xys]
      TangoLN t -> t & LN.foldTango \case
        NZF -> App alg $ Ctr "NZ" Unit
        CZF x xs -> App alg $ Ctr "CZ" $ Tuple [x, List xs]
        NSF n -> App alg $ Ctr "NS" $ Nat n
        CSF x xns -> App alg $ Ctr "CS" $ Tuple [x, xns]
      e -> error $ "cata is not defined for expressions of the form " ++ show (() <$ e)
    appPara :: Program h -> Program h -> Program h
    appPara alg = \case
      List xs -> paraList (\y (ys, r) -> App alg $ Cons y $ Tuple [r, List ys]) (App alg Nil) xs
      Tree xs -> paraTree (\l t y r u -> App alg $ Ctr "Node" $ Tuple [Tuple [l, Tree t], y, Tuple [r, Tree u]]) (App alg . Ctr "Leaf") xs
      Nat   n -> paraNat (\(i, r) -> App alg $ Ctr "Succ" $ Tuple [r, Nat i]) (App alg (Nat 0)) n
      e -> error $ "para is not defined for expressions of the form " ++ show (() <$ e)

-- Smart constructors

asProgram :: Expr l h -> Program h
asProgram = Unsafe.unsafeCoerce

-- * Values

-- NOTE: these form a prism
isValue :: Expr l h -> Maybe Value
isValue = \case
  Tuple xs -> Tuple <$> traverse isValue xs
  Ctr c x -> Ctr c <$> isValue x
  Lit i -> Just $ Lit i
  Var _ -> Nothing
  Lam _ _ -> Nothing
  App _ _ -> Nothing
  Prj _ _ -> Nothing
  Elim _ -> Nothing
  Hole _ -> Nothing

pattern Value :: Value -> Expr l h
pattern Value v <- (isValue -> Just v)
  where Value v = valueToExpr v

valueToExpr :: Value -> Expr l h
valueToExpr = \case
  Hole v -> absurd v
  e -> Unsafe.unsafeCoerce e

-- * Units

pattern Unit :: Expr l h
pattern Unit = Tuple []

-- * Applications

unApps :: Expr l h -> (Expr l h, [Expr l h])
unApps = \case
  App f e -> second (++ [e]) $ unApps f
  e -> (e, [])

{-# COMPLETE Apps #-}
pattern Apps :: Program h -> [Program h] -> Program h
pattern Apps f xs <- (unApps -> (f, xs))
  where Apps f xs = foldl' App f xs

-- * Lambdas

unLams :: Expr l h -> ([Name], Expr l h)
unLams = \case
  Lam x e -> first (x:) $ unLams e
  e -> ([], e)

{-# COMPLETE Lams #-}
pattern Lams :: [Name] -> Program h -> Program h
pattern Lams xs e <- (unLams -> (xs, e))
  where Lams xs e = foldr Lam e xs

lets :: [Named (Program h)] -> Program h -> Program h
lets bindings body = Apps (Lams vars body) args
  where
    vars = map (.name)  bindings
    args = map (.value) bindings

-- * Pattern matching

pattern Case :: () => (l ~ True) => Expr l h -> [(Name, Expr l h)] -> Expr l h
pattern Case e xs = App (Elim xs) e

pattern If :: () => (l ~ True) => Expr l h -> Expr l h -> Expr l h -> Expr l h
pattern If b t f = Case b [("True", t), ("False", f)]

-- * Lists

pattern Nil :: Expr l h
pattern Nil = Ctr "[]" Unit

pattern Cons :: Expr l h -> Expr l h -> Expr l h
pattern Cons x xs = Ctr ":" (Tuple [x, xs])

pattern List :: [Expr l h] -> Expr l h
pattern List xs <- (fromExpr -> Just xs)
  where List xs = toExpr _ xs

-- * Trees

pattern Tree :: Tree (Expr l h) (Expr l h) -> Expr l h
pattern Tree t <- (fromExpr -> Just t)
  where Tree t = toExpr _ t

-- * Nats

pattern Zero :: Expr l h
pattern Zero = Ctr "Zero" Unit

pattern Succ :: Expr l h -> Expr l h
pattern Succ n = Ctr "Succ" n

pattern Nat :: Nat -> Expr l h
pattern Nat n <- (fromExpr -> Just n)
  where Nat n = toExpr _ n

-- * Bools

pattern Bool :: Bool -> Expr l h
pattern Bool b <- (fromExpr -> Just b)
  where Bool b = toExpr _ b

-- * Orderings

pattern Ordering :: Ordering -> Expr l h
pattern Ordering o <- (fromExpr -> Just o)
  where Ordering o = toExpr _ o

-- * Tango

pattern TangoLL :: TangoListList (Expr l h) (Expr l h) -> Expr l h
pattern TangoLL xys <- (fromExpr -> Just xys)
  where TangoLL xys = toExpr _ xys

pattern TangoLN :: TangoListNat (Expr l h) -> Expr l h
pattern TangoLN xys <- (fromExpr -> Just xys)
  where TangoLN xys = toExpr _ xys

symbolName :: forall s -> KnownSymbol s => Name
symbolName s = fromString . symbolVal $ Proxy @s

-- * Generic instances

-- | Turn a Haskell container into an `Expr` (embedding).
class ToExpr l h a where
  toExpr :: forall t -> (t ~ a) => a -> Expr l h

  default toExpr :: (Generic a, GToExpr l h (Rep a)) => forall t -> (t ~ a) => a -> Expr l h
  toExpr _ = gtoExpr . from

type ToValue = ToExpr False Void

toValue :: forall a -> ToValue a => a -> Value
toValue t = toExpr t

instance ToExpr l h (Expr l h) where
  toExpr _ = id

instance ToExpr l h Int where
  toExpr _ = Lit . MkInt

instance ToExpr l h Nat where
  toExpr _ 0 = Zero
  toExpr _ n = Succ $ toExpr _ (n - 1)

instance ToExpr l h () where
  toExpr _ () = Unit

instance (ToExpr l h a, ToExpr l h b) => ToExpr l h (a, b) where
  toExpr _ (x, y) = Tuple [toExpr _ x, toExpr _ y]

instance (ToExpr l h a, ToExpr l h b, ToExpr l h c) => ToExpr l h (a, b, c) where
  toExpr _ (x, y, z) = Tuple [toExpr _ x, toExpr _ y, toExpr _ z]

-- instance ToExpr l h ()
instance ToExpr l h Bool
instance ToExpr l h Ordering
instance ToExpr l h a => ToExpr l h (Maybe a)
instance ToExpr l h a => ToExpr l h [a]
instance (ToExpr l h a) => ToExpr l h (TangoListNat a)
instance (ToExpr l h a, ToExpr l h b) => ToExpr l h (Either a b)
instance (ToExpr l h a, ToExpr l h b) => ToExpr l h (Tree a b)
instance (ToExpr l h a, ToExpr l h b) => ToExpr l h (TangoListList a b)

instance ToExpr l h a => ToExpr l h (SortedList a) where
  toExpr _ (Sorted xs) = toExpr _ xs

class GToExpr l h f where
  gtoExpr :: f a -> Expr l h

instance GToExpr l h U1 where
  gtoExpr _ = Unit

instance ToExpr l h c => GToExpr l h (K1 i c) where
  gtoExpr (K1 c) = toExpr (type c) c

instance GToExpr l h f => GToExpr l h (D1 c f) where
  gtoExpr (M1 p) = gtoExpr p

instance GToExpr l h f => GToExpr l h (S1 c f) where
  gtoExpr (M1 p) = gtoExpr p

instance (KnownSymbol c, GToExpr l h f) => GToExpr l h (C1 (MetaCons c g s) f) where
  gtoExpr (M1 p) = Ctr (symbolName c) $ gtoExpr p

instance (GToExpr l h a, GToExpr l h b) => GToExpr l h (a :+: b) where
  gtoExpr (L1 p) = gtoExpr p
  gtoExpr (R1 p) = gtoExpr p

instance (GToExpr l h a, GToExpr l h b) => GToExpr l h (a :*: b) where
  gtoExpr (a :*: b) = tuple $ gtoExpr a : projections (gtoExpr b)

-- | Turn a `Value` into a Haskell value of type `a` (extraction).
class FromExpr l h a where
  fromExpr :: Expr l h -> Maybe a

  default fromExpr :: (Generic a, GFromExpr l h (Rep a)) => Expr l h -> Maybe a
  fromExpr = fmap to . gfromExpr

type FromValue = FromExpr False Void

fromValue :: forall a -> FromValue a => Value -> Maybe a
fromValue _ = fromExpr

instance FromExpr l h (Expr l h) where
  fromExpr = Just

instance FromExpr l h Int where
  fromExpr = \case
    Lit (MkInt i) -> Just i
    _ -> Nothing

instance FromExpr l h Nat where
  fromExpr = \case
    Zero -> Just 0
    Succ n -> (1+) <$> fromExpr n
    _ -> Nothing

instance FromExpr l h () where
  fromExpr = \case
    Unit -> Just ()
    _ -> Nothing

instance (FromExpr l h a, FromExpr l h b) => FromExpr l h (a, b) where
  fromExpr = \case
    Tuple [x, y] -> liftA2 (,) (fromExpr x) (fromExpr y)
    _ -> Nothing

instance (FromExpr l h a, FromExpr l h b, FromExpr l h c) => FromExpr l h (a, b, c) where
  fromExpr = \case
    Tuple [x, y, z] -> liftA3 (,,) (fromExpr x) (fromExpr y) (fromExpr z)
    _ -> undefined

-- instance FromExpr l h ()
instance FromExpr l h Bool
instance FromExpr l h Ordering
instance FromExpr l h a => FromExpr l h (Maybe a)
instance FromExpr l h a => FromExpr l h [a]
instance FromExpr l h a => FromExpr l h (TangoListNat a)
instance (FromExpr l h a, FromExpr l h b) => FromExpr l h (Either a b)
instance (FromExpr l h a, FromExpr l h b) => FromExpr l h (Tree a b)
instance (FromExpr l h a, FromExpr l h b) => FromExpr l h (TangoListList a b)

instance FromExpr l h a => FromExpr l h (SortedList a) where
  fromExpr xs = Sorted <$> fromExpr xs

class GFromExpr l h f where
  gfromExpr :: Expr l h -> Maybe (f a)

instance GFromExpr l h U1 where
  gfromExpr = \case
    Unit -> Just U1
    _ -> Nothing

instance FromExpr l h c => GFromExpr l h (K1 i c) where
  gfromExpr = fmap K1 . fromExpr

instance GFromExpr l h f => GFromExpr l h (D1 c f) where
  gfromExpr = fmap M1 . gfromExpr

instance GFromExpr l h f => GFromExpr l h (S1 c f) where
  gfromExpr = fmap M1 . gfromExpr

instance (KnownSymbol c, GFromExpr l h f) => GFromExpr l h (C1 (MetaCons c g s) f) where
  gfromExpr = \case
    Ctr d e | d == symbolName c -> M1 <$> gfromExpr e
    _ -> Nothing

instance (GFromExpr l h a, GFromExpr l h b) => GFromExpr l h (a :+: b) where
  gfromExpr e = case gfromExpr e of
    Just x -> Just $ L1 x
    Nothing -> R1 <$> gfromExpr e

instance (GFromExpr l h a, GFromExpr l h b) => GFromExpr l h (a :*: b) where
  gfromExpr = \case
    Tuple (x:xs) -> liftA2 (:*:) (gfromExpr x) (gfromExpr $ tuple xs)
    _ -> Nothing

-- | Interpret a program as a Haskell function.
class Interpret a where
  interpret :: Program Void -> a

instance {-# OVERLAPPING #-} FromExpr False Void a => Interpret a where
  interpret e = case normalize e of
    Value v -> case fromExpr v of
      Nothing -> error $ "Not a value: " ++ show v
      Just x -> x
    _ -> error "normalized expression is not a value"

instance {-# OVERLAPPING #-}
  (ToValue a, Interpret b) => Interpret (a -> b) where
  interpret p = interpret . App p . Value . toValue a

-- | Execute a Haskell function on a list of values.
class Execute a where
  execute :: a -> [Value] -> Value

instance {-# OVERLAPPING #-} ToValue a => Execute a where
  execute (toValue a -> v) [] = v
  execute _ _ = error "Either not a value, or too many arguments"

instance {-# OVERLAPPING #-} (FromValue a, Execute b) => Execute (a -> b) where
  execute _ [] = error "Not enough arguments"
  execute f (x:xs) = case fromValue a x of
    Nothing -> error $ show x <> " not a valid expression"
    Just e -> execute (f e) xs
