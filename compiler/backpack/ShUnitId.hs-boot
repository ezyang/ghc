module ShUnitId where
import {-# SOURCE #-} Module (Module, ModuleName, UnitId, ComponentId)
import {-# SOURCE #-} DynFlags (DynFlags)
import Outputable (SDoc)
newUnitId :: DynFlags
          -> ComponentId
          -> [(ModuleName, Module)] -- hole instantiations
          -> IO UnitId
pprUnitId :: UnitId -> SDoc
