module Packages where
-- Well, this is kind of stupid...
import {-# SOURCE #-} Module (UnitKey)
import {-# SOURCE #-} DynFlags (DynFlags)
data PackageState
unitKeyPackageIdString :: DynFlags -> UnitKey -> Maybe String
emptyPackageState :: PackageState
