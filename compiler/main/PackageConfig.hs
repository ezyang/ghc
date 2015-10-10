{-# LANGUAGE CPP, RecordWildCards, FlexibleInstances #-}

-- |
-- Package configuration information: essentially the interface to Cabal, with
-- some utilities
--
-- (c) The University of Glasgow, 2004
--
module PackageConfig (
        -- $package_naming

        -- * UnitId
        packageConfigId,

        -- * The PackageConfig type: information about a package
        PackageConfig,
        InstalledPackageInfo(..),
        ComponentId(..),
        SourcePackageId(..),
        PackageName(..),
        ComponentName(..),
        Version(..),
        defaultPackageConfig,
        componentIdString,
        sourcePackageIdString,
        packageNameString,
        pprPackageConfig,

        packageComponentName,
        packageComponentId,

        -- * Hack.
        addComponentName,

        -- * Package key
        ShUnitId(..),
    ) where

#include "HsVersions.h"

import GHC.PackageDb
import Data.Version

import {-# SOURCE #-} Packages
import FastString
import Outputable
import Module
import Unique
import UniqSet

-- -----------------------------------------------------------------------------
-- Our PackageConfig type is the InstalledPackageInfo from ghc-boot,
-- which is similar to a subset of the InstalledPackageInfo type from Cabal.

type PackageConfig = InstalledPackageInfo
                       ComponentId
                       SourcePackageId
                       PackageName
                       Module.UnitId
                       ComponentName
                       Module.ModuleName

-- TODO: there's no need for these to be FastString, as we don't need the uniq
--       feature, but ghc doesn't currently have convenient support for any
--       other compact string types, e.g. plain ByteString or Text.

newtype ComponentId        = ComponentId        FastString deriving (Eq, Ord)
newtype SourcePackageId    = SourcePackageId    FastString deriving (Eq, Ord)
newtype PackageName        = PackageName        FastString deriving (Eq, Ord)
newtype ComponentName      = ComponentName      FastString deriving (Eq, Ord)

instance BinaryStringRep ComponentId where
  fromStringRep = ComponentId . mkFastStringByteString
  toStringRep (ComponentId s) = fastStringToByteString s

instance BinaryStringRep SourcePackageId where
  fromStringRep = SourcePackageId . mkFastStringByteString
  toStringRep (SourcePackageId s) = fastStringToByteString s

instance BinaryStringRep PackageName where
  fromStringRep = PackageName . mkFastStringByteString
  toStringRep (PackageName s) = fastStringToByteString s

instance BinaryStringRep ComponentName where
  fromStringRep = ComponentName . mkFastStringByteString
  toStringRep (ComponentName s) = fastStringToByteString s

instance Uniquable ComponentId where
  getUnique (ComponentId n) = getUnique n

instance Uniquable SourcePackageId where
  getUnique (SourcePackageId n) = getUnique n

instance Uniquable PackageName where
  getUnique (PackageName n) = getUnique n

instance Outputable ComponentId where
  ppr cid@(ComponentId str) =
    sdocWithDynFlags $ \dflags ->
        case lookupComponentIdString dflags cid of
            Nothing -> ftext str
            Just spid -> text spid

instance Outputable ComponentName where
  ppr (ComponentName str) = ftext str

instance Outputable SourcePackageId where
  ppr (SourcePackageId str) = ftext str

instance Outputable PackageName where
  ppr (PackageName str) = ftext str

-- | Pretty-print an 'GenModule' in the same format used by the textual
-- installed package database. (TODO: Actually not really)
pprGenModule :: (Outputable a, Outputable b) => GenModule a b -> SDoc
pprGenModule (Module a b) =
    ppr a <> char ':' <> ppr b

defaultPackageConfig :: PackageConfig
defaultPackageConfig = emptyInstalledPackageInfo

componentIdString :: PackageConfig -> String
componentIdString pkg = unpackFS str
  where
    ComponentId str = componentId pkg

sourcePackageIdString :: PackageConfig -> String
sourcePackageIdString pkg = unpackFS str
  where
    SourcePackageId str = sourcePackageId pkg

packageNameString :: PackageConfig -> String
packageNameString pkg = unpackFS str
  where
    PackageName str = packageName pkg

pprPackageConfig :: PackageConfig -> SDoc
pprPackageConfig InstalledPackageInfo {..} =
    vcat [
      field "name"                 (ppr packageName),
      field "version"              (text (showVersion packageVersion)),
      field "id"                   (ppr componentId),
      field "exposed"              (ppr exposed),
      field "exposed-modules"      (ppr exposedModules),
      field "hidden-modules"       (fsep (map ppr hiddenModules)),
      field "trusted"              (ppr trusted),
      field "import-dirs"          (fsep (map text importDirs)),
      field "library-dirs"         (fsep (map text libraryDirs)),
      field "hs-libraries"         (fsep (map text hsLibraries)),
      field "extra-libraries"      (fsep (map text extraLibraries)),
      field "extra-ghci-libraries" (fsep (map text extraGHCiLibraries)),
      field "include-dirs"         (fsep (map text includeDirs)),
      field "includes"             (fsep (map text includes)),
      field "depends"              (fsep (map ppr  depends)),
      field "cc-options"           (fsep (map text ccOptions)),
      field "ld-options"           (fsep (map text ldOptions)),
      field "framework-dirs"       (fsep (map text frameworkDirs)),
      field "frameworks"           (fsep (map text frameworks)),
      field "haddock-interfaces"   (fsep (map text haddockInterfaces)),
      field "haddock-html"         (fsep (map text haddockHTMLs))
    ]
  where
    field name body = text name <> colon <+> nest 4 body

-- -----------------------------------------------------------------------------
-- UnitId (package names, versions and dep hash)

-- $package_naming
-- #package_naming#
-- Mostly the compiler deals in terms of 'UnitId's, which are md5 hashes
-- of a package ID, keys of its dependencies, and Cabal flags. You're expected
-- to pass in the unit id in the @-this-package-key@ flag. However, for
-- wired-in packages like @base@ & @rts@, we don't necessarily know what the
-- version is, so these are handled specially; see #wired_in_packages#.

-- | Get the GHC 'UnitId' right out of a Cabalish 'PackageConfig'
packageConfigId :: PackageConfig -> UnitId
packageConfigId = unitId

-- | This defaults the unit name of a package to its package name, if
-- it's an old-style one.
packageComponentName :: PackageConfig -> ComponentName
packageComponentName pkg = componentName pkg

-- TODO rename me
packageComponentId :: PackageConfig -> ComponentId
packageComponentId pkg = componentId pkg

{-
************************************************************************
*                                                                      *
                        Indefinite package
*                                                                      *
************************************************************************
-}

addComponentName :: ComponentId -> ComponentName -> ComponentId
addComponentName (ComponentId cid) (ComponentName n) =
    ComponentId (concatFS [cid, fsLit "-", n])

-- | An elaborated representation of a 'UnitId', which records
-- all of the components that go into the hashed 'UnitId'.
data ShUnitId
    = ShUnitId {
          shUnitIdComponentId       :: !ComponentId,
          shUnitIdInsts             :: ![(ModuleName, Module)],
          shUnitIdFreeHoles         :: UniqSet ModuleName
      }

instance Eq ShUnitId where
    suid == suid' = shUnitIdComponentId suid == shUnitIdComponentId suid'
                 && shUnitIdInsts suid == shUnitIdInsts suid'

instance Outputable ShUnitId where
    ppr (ShUnitId uid insts fh)
        = ppr uid <+> ppr insts <+> parens (ppr fh)
