module ShPackageKey where
import {-# SOURCE #-} PackageConfig (PackageName, LibraryName)
import {-# SOURCE #-} Module (Module, ModuleName, PackageKey)
import {-# SOURCE #-} DynFlags (DynFlags)
import Outputable (SDoc)
newPackageKey :: DynFlags
              -> PackageName
              -> LibraryName
              -> [(ModuleName, Module)] -- hole instantiations
              -> IO PackageKey
pprPackageKey :: PackageKey -> SDoc
