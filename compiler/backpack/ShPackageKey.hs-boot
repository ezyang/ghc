module ShPackageKey where
import PackageConfig (PackageName, VersionHash)
import Module (Module, ModuleName, PackageKey)
import {-# SOURCE #-} DynFlags (DynFlags)
newPackageKey :: DynFlags
              -> PackageName
              -> VersionHash
              -> [(ModuleName, Module)] -- hole instantiations
              -> IO PackageKey
