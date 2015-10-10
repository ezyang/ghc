module Packages where
import {-# SOURCE #-} PackageConfig (ComponentId)
import {-# SOURCE #-} DynFlags (DynFlags)
data PackageState
emptyPackageState :: PackageState
lookupComponentIdString :: DynFlags -> ComponentId -> Maybe String
