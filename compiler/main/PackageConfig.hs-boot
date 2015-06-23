module PackageConfig where
import FastString
newtype PackageName = PackageName FastString
newtype VersionHash = VersionHash FastString
