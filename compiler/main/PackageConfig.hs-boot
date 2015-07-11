module PackageConfig where
import FastString
newtype PackageName = PackageName FastString
newtype LibraryName = LibraryName FastString
