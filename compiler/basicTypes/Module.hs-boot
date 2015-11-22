module Module(module Module, moduleName, moduleUnitId) where

import GHC.PackageDb (GenModule(..))
import FastString

type Module = GenModule UnitId ModuleName
data ModuleName
data UnitId
newtype ComponentId = ComponentId FastString
unitIdString :: UnitId -> String
