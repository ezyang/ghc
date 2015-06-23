module ShPackageKey where
import {-# SOURCE #-} PackageConfig (UnitName, LibraryName)
import {-# SOURCE #-} Module (Module, ModuleName, PackageKey)
import {-# SOURCE #-} DynFlags (DynFlags)
import Outputable (SDoc)
newPackageKey :: DynFlags
              -> UnitName
              -> LibraryName
              -> [(ModuleName, Module)] -- hole instantiations
              -> IO PackageKey
pprPackageKey :: PackageKey -> SDoc
