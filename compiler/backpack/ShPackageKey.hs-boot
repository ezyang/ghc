module ShPackageKey where
import {-# SOURCE #-} PackageConfig (PackageName, VersionHash)
import {-# SOURCE #-} Module (Module, ModuleName, PackageKey)
import {-# SOURCE #-} DynFlags (DynFlags)
import Outputable (SDoc)
newPackageKey :: DynFlags
              -> PackageName
              -> VersionHash
              -> [(ModuleName, Module)] -- hole instantiations
              -> IO PackageKey
pprPackageKey :: PackageKey -> SDoc
