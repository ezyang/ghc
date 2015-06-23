module PackageConfig where
import FastString
import GHC.PackageDb
newtype PackageName = PackageName FastString
newtype UnitName = UnitName FastString
newtype InstalledPackageId = InstalledPackageId FastString
type IndefUnitId = IndefiniteUnitId InstalledPackageId UnitName
