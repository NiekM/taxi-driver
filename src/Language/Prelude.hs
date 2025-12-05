module Language.Prelude (datatypes) where

import Base hiding (Nat)
import GHC.Generics

import Data.Tree.Binary
import Data.Tango.List.List
import Data.Tango.List.Nat

import Language.Type

data Nat
  = Zero
  | Succ Nat
  deriving (Eq, Ord, Show, Generic)

datatypes :: DataContext
datatypes = DataContext $
  [ toData Bool
  , toData Ordering
  , toData Nat
  , toData Maybe
  , toData (type [])
  , toData Either
  , toData Tree
  , toData TangoListList
  , toData TangoListNat
  ] >>= \d -> d : maybeToList (base d)
