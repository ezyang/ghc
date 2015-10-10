module Module where
import FastString

data Module
data ModuleName
data UnitId
newtype ComponentId = ComponentId FastString

moduleName :: Module -> ModuleName
moduleUnitId :: Module -> UnitId
unitIdString :: UnitId -> String
