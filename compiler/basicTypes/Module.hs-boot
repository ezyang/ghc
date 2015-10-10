module Module(module Module, moduleName, moduleUnitId) where

import GHC.PackageDb (GenModule(..))

type Module = GenModule UnitId ModuleName
data ModuleName
data UnitId
unitIdString :: UnitId -> String
