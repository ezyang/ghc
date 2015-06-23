module ShUnitKey where
import {-# SOURCE #-} PackageConfig (IndefUnitId)
import {-# SOURCE #-} Module (Module, ModuleName, UnitKey)
import {-# SOURCE #-} DynFlags (DynFlags)
import Outputable (SDoc)
newUnitKey :: DynFlags
              -> IndefUnitId
              -> [(ModuleName, Module)] -- hole instantiations
              -> IO UnitKey
pprUnitKey :: UnitKey -> SDoc
