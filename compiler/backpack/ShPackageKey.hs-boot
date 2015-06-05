module ShPackageKey where

import {-# SOURCE #-} Module (PackageKey)
import Outputable

pprPackageKey :: PackageKey -> SDoc
