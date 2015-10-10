module ShUnitId where
import {-# SOURCE #-} PackageConfig (ComponentId)
import {-# SOURCE #-} Module (Module, ModuleName, UnitId)
import {-# SOURCE #-} DynFlags (DynFlags)
import Outputable (SDoc)
newUnitId :: DynFlags
          -> ComponentId
          -> [(ModuleName, Module)] -- hole instantiations
          -> IO UnitId
pprUnitId :: UnitId -> SDoc
