module Tactic.Extract where

import Tactic.Core
import Tactic.Constructors
import Tactic.Elim
import Tactic.Relation

greedyStep :: Tactic sig m => m Filling
greedyStep = anywhereBiased assume <| constructors <| anywhereBiased elim <| anywhereBiased2 relations

extract :: Tactic sig m => m Filling
extract = repeat greedyStep
