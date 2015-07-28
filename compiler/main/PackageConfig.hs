{-# LANGUAGE CPP, RecordWildCards #-}

-- |
-- Package configuration information: essentially the interface to Cabal, with
-- some utilities
--
-- (c) The University of Glasgow, 2004
--
module PackageConfig (
        -- $package_naming

        -- * UnitKey
        packageConfigId,

        -- * The PackageConfig type: information about a package
        PackageConfig,
        InstalledPackageInfo(..),
        InstalledPackageId(..),
        SourcePackageId(..),
        PackageName(..),
        UnitName(..),
        Version(..),
        defaultPackageConfig,
        installedPackageIdString,
        sourcePackageIdString,
        packageNameString,
        pprPackageConfig,

        packageUnitName,
        packageUnitId,

        -- * Indefinite packages
        IndefiniteUnitConfig(..), indefShUnitKey,
        IndefiniteUnitId(..),

        -- * Package key
        ShUnitKey(..),
    ) where

#include "HsVersions.h"

import GHC.PackageDb
import Data.Version

import FastString
import Outputable
import Module
import Unique
import UniqSet

import Data.Maybe
import Data.Map (Map)

-- -----------------------------------------------------------------------------
-- Our PackageConfig type is the InstalledPackageInfo from bin-package-db,
-- which is similar to a subset of the InstalledPackageInfo type from Cabal.

type PackageConfig = InstalledPackageInfo
                       InstalledPackageId
                       SourcePackageId
                       PackageName
                       Module.UnitKey
                       UnitName
                       Module.ModuleName

-- TODO: there's no need for these to be FastString, as we don't need the uniq
--       feature, but ghc doesn't currently have convenient support for any
--       other compact string types, e.g. plain ByteString or Text.

newtype InstalledPackageId = InstalledPackageId FastString deriving (Eq, Ord)
newtype SourcePackageId    = SourcePackageId    FastString deriving (Eq, Ord)
newtype PackageName        = PackageName        FastString deriving (Eq, Ord)
newtype UnitName           = UnitName           FastString deriving (Eq, Ord)

instance BinaryStringRep InstalledPackageId where
  fromStringRep = InstalledPackageId . mkFastStringByteString
  toStringRep (InstalledPackageId s) = fastStringToByteString s

instance BinaryStringRep SourcePackageId where
  fromStringRep = SourcePackageId . mkFastStringByteString
  toStringRep (SourcePackageId s) = fastStringToByteString s

instance BinaryStringRep PackageName where
  fromStringRep = PackageName . mkFastStringByteString
  toStringRep (PackageName s) = fastStringToByteString s

instance BinaryStringRep UnitName where
  fromStringRep = UnitName . mkFastStringByteString
  toStringRep (UnitName s) = fastStringToByteString s

instance Uniquable InstalledPackageId where
  getUnique (InstalledPackageId n) = getUnique n

instance Uniquable SourcePackageId where
  getUnique (SourcePackageId n) = getUnique n

instance Uniquable PackageName where
  getUnique (PackageName n) = getUnique n

instance Outputable InstalledPackageId where
  ppr (InstalledPackageId str) = ftext str

instance Outputable UnitName where
  ppr (UnitName str) = ftext str

instance Outputable SourcePackageId where
  ppr (SourcePackageId str) = ftext str

instance Outputable PackageName where
  ppr (PackageName str) = ftext str

-- | Pretty-print an 'ExposedModule' in the same format used by the textual
-- installed package database.
pprExposedModule :: (Outputable a, Outputable b) => ExposedModule a b -> SDoc
pprExposedModule (ExposedModule exposedName exposedReexport exposedSignature) =
    sep [ ppr exposedName
        , case exposedReexport of
            Just m -> sep [text "from", pprOriginalModule m]
            Nothing -> empty
        , case exposedSignature of
            Just m -> sep [text "is", pprOriginalModule m]
            Nothing -> empty
        ]

-- | Pretty-print an 'OriginalModule' in the same format used by the textual
-- installed package database.
pprOriginalModule :: (Outputable a, Outputable b) => OriginalModule a b -> SDoc
pprOriginalModule (OriginalModule originalPackageId originalModuleName) =
    ppr originalPackageId <> char ':' <> ppr originalModuleName

defaultPackageConfig :: PackageConfig
defaultPackageConfig = emptyInstalledPackageInfo

installedPackageIdString :: PackageConfig -> String
installedPackageIdString pkg = unpackFS str
  where
    InstalledPackageId str = installedPackageId pkg

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
      field "id"                   (ppr unitKey),
      field "package-id"           (ppr installedPackageId),
      field "exposed"              (ppr exposed),
      field "exposed-modules"
        (if all isExposedModule exposedModules
           then fsep (map pprExposedModule exposedModules)
           else pprWithCommas pprExposedModule exposedModules),
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
    isExposedModule (ExposedModule _ Nothing Nothing) = True
    isExposedModule _ = False


-- -----------------------------------------------------------------------------
-- UnitKey (package names, versions and dep hash)

-- $package_naming
-- #package_naming#
-- Mostly the compiler deals in terms of 'UnitKey's, which are md5 hashes
-- of a package ID, keys of its dependencies, and Cabal flags. You're expected
-- to pass in the unit key in the @-this-unit-key@ flag. However, for
-- wired-in packages like @base@ & @rts@, we don't necessarily know what the
-- version is, so these are handled specially; see #wired_in_packages#.

-- | Get the GHC 'UnitKey' right out of a Cabalish 'PackageConfig'
packageConfigId :: PackageConfig -> UnitKey
packageConfigId = unitKey

packageUnitName :: PackageConfig -> UnitName
packageUnitName pkg = let PackageName fs = packageName pkg
                      in fromMaybe (UnitName fs) (unitName pkg)

packageUnitId :: PackageConfig -> IndefiniteUnitId
packageUnitId pkg = IndefiniteUnitId (installedPackageId pkg) (unitName pkg)

{-
************************************************************************
*                                                                      *
                        Indefinite package
*                                                                      *
************************************************************************
-}

-- | 'IndefiniteUnitConfig' is analogous to 'PackageConfig', except it stores
-- information on indefinite packages.  (Note: definite packages are also
-- "indefinite", they just have no requirements and are pre-built.)
-- TODO: if we write this to disk we have to recover all the package keys!!
-- NB: source code not recorded here, you get it elsewhere
data IndefiniteUnitConfig = IndefiniteUnitConfig {
            indefUnitId   :: IndefiniteUnitId,
            indefProvides :: Map ModuleName Module,
            indefRequires :: [ModuleName]
        }

instance Outputable IndefiniteUnitConfig where
    ppr unit = ppr (indefUnitId unit) $$ ppr (indefProvides unit) $$ ppr (indefRequires unit)

-- | Computes the 'ShUnitKey' of an 'IndefiniteUnitConfig',
-- assuming all the holes are unfilled.
indefShUnitKey :: IndefiniteUnitConfig -> ShUnitKey
indefShUnitKey IndefiniteUnitConfig {
                    indefUnitId = uid,
                    indefRequires = requires
                  } = ShUnitKey {
                    shUnitKeyUnitId = uid,
                    shUnitKeyInsts = [ (m, mkModule holeUnitKey m)
                                        | m <- requires],
                    shUnitKeyFreeHoles = mkUniqSet requires
                  }

-- | An unit ID uniquely identifies an indefinite unit in the indefinite
-- unit database.  If 'indefUnitName' is 'Nothing', this is an old-style
-- package (required to have no holes.)
data IndefiniteUnitId
    = IndefiniteUnitId { indefUnitIPID :: InstalledPackageId
                       , indefUnitName :: Maybe UnitName }
    deriving (Eq, Ord)

instance Outputable IndefiniteUnitId where
    ppr (IndefiniteUnitId ipid Nothing) =
        ppr ipid -- it's the IPID
    ppr (IndefiniteUnitId ipid (Just unit)) =
        -- TODO: qualification logic
        ppr unit <> ifPprDebug (braces (ppr ipid))

-- | An elaborated representation of a 'UnitKey', which records
-- all of the components that go into the hashed 'UnitKey'.
data ShUnitKey
    = ShUnitKey {
          shUnitKeyUnitId            :: !IndefiniteUnitId,
          shUnitKeyInsts             :: ![(ModuleName, Module)],
          shUnitKeyFreeHoles         :: UniqSet ModuleName
      }
    deriving Eq

instance Outputable ShUnitKey where
    ppr (ShUnitKey uid insts fh)
        = ppr uid <+> ppr insts <+> parens (ppr fh)
