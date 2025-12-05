module Tactic.Options (RealizabilityLevel(..), TacticOptions(..)) where

import Base

data RealizabilityLevel
  = NoRealizability
  | MonoRealizability
  | PolyRealizability
  deriving stock (Eq, Ord, Show, Read, Enum, Bounded)

data TacticOptions = TacticOptions
  { removeDuplicates   :: Bool
  , checkCoverage      :: Bool
  , reconstructProblem :: Bool
  , conditionalBranch  :: Bool
  , realizabilityLevel :: RealizabilityLevel
  } deriving stock (Eq, Ord, Show, Read)

instance Default TacticOptions where
  def = TacticOptions
    { removeDuplicates   = True
    , checkCoverage      = True
    , reconstructProblem = True
    , conditionalBranch  = True
    , realizabilityLevel = PolyRealizability
    }
