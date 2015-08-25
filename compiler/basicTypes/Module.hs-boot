module Module where

data Module
data ModuleName
data UnitKey
moduleName :: Module -> ModuleName
moduleUnitKey :: Module -> UnitKey
unitKeyString :: UnitKey -> String
