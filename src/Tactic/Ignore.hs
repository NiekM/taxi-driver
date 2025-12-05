module Tactic.Ignore where

import Base

import Language.Spec

import Tactic.Check
import Tactic.Core
import Tactic.Hole

ignore :: Tactic sig m => Name -> m Filling
ignore name = local (hide [name]) $ rerealize hole
