module Packages where
-- Well, this is kind of stupid...
import {-# SOURCE #-} Module (PackageKey)
import PprFlags (PprFlags)
data PackageState
packageKeyPackageIdString :: PprFlags -> PackageKey -> String
