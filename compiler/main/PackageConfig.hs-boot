module PackageConfig where
import FastString
newtype PackageName = PackageName FastString
newtype UnitName = UnitName FastString
newtype LibraryName = LibraryName FastString
data IndefiniteUnitId
