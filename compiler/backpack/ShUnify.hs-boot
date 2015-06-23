module ShUnify where

import DynFlags
import Module
import UniqSet

mkShHoleSubst :: DynFlags -> ModuleNameEnv Module
              -> IO (ModuleNameEnv (Module, UniqSet ModuleName))
