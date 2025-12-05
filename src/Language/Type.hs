{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Type where

import GHC.Generics hiding (Constructor)
import GHC.TypeLits (KnownSymbol, symbolVal)
import Data.Kind (Type)
import Data.Proxy

import Data.Functor.Compose
import Data.Monoid (Any(..))
import Data.List qualified as List
import Data.Set qualified as Set

import Base

-- We could try to design our framework to be generic over the types and
-- expressions, by creating some type class that provides e.g. a lens to the
-- polymorphic variables. The specific datatypes used can decide how
-- deep/shallow and typed/untyped their embedding is, as long as they provide
-- the right interface.
data Mono where
  Free :: Name -> Mono
  Product :: [Mono] -> Mono
  Data :: Name -> [Mono] -> Mono
  Base :: Base -> Mono
  deriving stock (Eq, Ord, Show)

pattern Top :: Mono
pattern Top = Product []

instance Project Mono where
  projections = \case
    Product ts -> ts
    t -> [t]

instantiate :: (Name -> Mono) -> Mono -> Mono
instantiate f = \case
  Free a -> f a
  Product ts -> Product (instantiate f <$> ts)
  Data d ts -> Data d (instantiate f <$> ts)
  Base b -> Base b

-- Base types
data Base = Int
  deriving stock (Eq, Ord, Show)

getFree :: Mono -> Set Name
getFree = \case
  Free a -> Set.singleton a
  Product ts -> foldMap getFree ts
  Data _ ts -> foldMap getFree ts
  Base _ -> Set.empty

type Constructor = Named Mono

data DataDef = DataDef
  { arguments :: [Name]
  , constructors :: [Constructor]
  } deriving stock (Eq, Ord, Show)

base :: Named DataDef -> Maybe (Named DataDef)
base (Named name definition)
  | recursive = Just $ Named (name <> "F") basedef
  | otherwise = Nothing
  where
    basedef = DataDef (definition.arguments ++ ["r"]) cs

    (Any recursive, Compose cs) = traverse locate (Compose definition.constructors)

    locate :: Mono -> (Any, Mono)
    locate = \case
      t | t == Data name (Free <$> definition.arguments) -> (Any True, Free "r")
      Product ts -> Product <$> traverse locate ts
      Data d ts -> Data d <$> traverse locate ts
      t -> (Any False, t)

newtype DataContext = DataContext
  { datatypes :: [Named DataDef]
  } deriving stock (Eq, Ord, Show)

getConstructors :: Name -> [Mono] -> DataContext -> [Constructor]
getConstructors name ts ctx =
  case find name ctx.datatypes of
    Nothing -> error $ "Unknown datatype " <> show name
    Just datatype ->
      let
        mapping var =
          fromMaybe (Free var) . List.lookup var $ zip datatype.arguments ts
      in datatype.constructors <&> \(Named c t) ->
        Named c (instantiate mapping t)

data Constraint = Eq Name | Ord Name
  deriving stock (Eq, Ord, Show)

data Signature = Signature
  { constraints :: [Constraint]
  , inputs      :: [Named Mono]
  , output      :: Mono
  } deriving stock (Eq, Ord, Show)

instance Project Signature where
  projections sig = do
    output <- projections sig.output
    return (sig { output } :: Signature)

-- | Types that can be represented as `Mono`.
class ToType a where
  toType :: forall b -> a ~ b => Mono

  default toType :: (Generic a, GToType (Rep a)) => forall b -> a ~ b => Mono
  toType _ = gtoType (Rep a)

data A deriving (Eq, Ord, Show, Generic)
data B deriving (Eq, Ord, Show, Generic)

instance ToType A where
  toType _ = Free "a"

instance ToType B where
  toType _ = Free "b"

instance ToType Int where
  toType _ = Base Int

dataName :: forall a -> DataName (Rep a) => Name
dataName a = dname (Rep a)

class DataName f where
  dname :: forall g -> f ~ g => Name

symbolName :: forall s -> KnownSymbol s => Name
symbolName s = fromString . symbolVal $ Proxy @s

instance KnownSymbol n => DataName (D1 (MetaData n m p nt) f) where
  dname _ = symbolName n

instance ToType Nat where
  toType _ = Data "Nat" []

instance {-# OVERLAPPABLE #-} DataName (Rep a) => ToType a where
  toType t = Data (dataName t) []

instance {-# OVERLAPPABLE #-} (DataName (Rep (f a)), ToType a) =>
  ToType (f a) where
  toType t = Data (dataName t) [toType a]

instance {-# OVERLAPPABLE #-} (DataName (Rep (f a b)), ToType a, ToType b) =>
  ToType (f a b) where
  toType t = Data (dataName t) [toType a, toType b]

class GToType f where
  gtoType :: forall g -> f ~ g => Mono

instance GToType U1 where
  gtoType _ = Top

instance ToType c => GToType (K1 i c) where
  gtoType _ = toType c

instance GToType f => GToType (S1 m f) where
  gtoType _ = gtoType f

instance (GToType f, GToType g) => GToType (f :*: g) where
  gtoType _ = Product $ gtoType f : projections (gtoType g)

-- | Compute the `DataDef` representation of a type `k`.
class ToData (f :: k) where
  toData :: forall g -> f ~ g => Named DataDef

instance GToData (Rep a) => ToData (a :: Type) where
  toData _ = gdatatype (Rep a) <&> DataDef []

instance (GToData (Rep (f A)), Generic (f A)) =>
  ToData (f :: Type -> Type) where
  toData _ = gdatatype (Rep (f A)) <&> DataDef ["a"]

instance (GToData (Rep (f A B)), Generic (f A B)) =>
  ToData (f :: Type -> Type -> Type) where
  toData _ = gdatatype (Rep (f A B)) <&> DataDef ["a", "b"]

-- TODO: it seems that this does not work if one of the constructors has the
-- same name as the type itself...
class GToData f where
  gdatatype :: forall g -> f ~ g => Named [Constructor]

instance (GConstructors f, KnownSymbol n) =>
  GToData (D1 (MetaData n m p nt) f) where
  gdatatype _ = Named (symbolName n) (gconstructors f)

class GConstructors f where
  gconstructors :: forall g -> f ~ g => [Constructor]

instance (KnownSymbol c, GToType f) =>
  GConstructors (C1 (MetaCons c g s) f) where
  gconstructors _ = [Named (symbolName c) (gtoType f)]

instance (GConstructors f, GConstructors g) => GConstructors (f :+: g) where
  gconstructors _ = gconstructors f ++ gconstructors g
