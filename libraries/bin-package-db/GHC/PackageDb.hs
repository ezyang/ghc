{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
-- This module deliberately defines orphan instances for now (Binary Version).
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-name-shadowing #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.PackageDb
-- Copyright   :  (c) The University of Glasgow 2009, Duncan Coutts 2014
--
-- Maintainer  :  ghc-devs@haskell.org
-- Portability :  portable
--
-- This module provides the view of GHC's database of registered packages that
-- is shared between GHC the compiler\/library, and the ghc-pkg program. It
-- defines the database format that is shared between GHC and ghc-pkg.
--
-- The database format, and this library are constructed so that GHC does not
-- have to depend on the Cabal library. The ghc-pkg program acts as the
-- gateway between the external package format (which is defined by Cabal) and
-- the internal package format which is specialised just for GHC.
--
-- GHC the compiler only needs some of the information which is kept about
-- registerd packages, such as module names, various paths etc. On the other
-- hand ghc-pkg has to keep all the information from Cabal packages and be able
-- to regurgitate it for users and other tools.
--
-- The first trick is that we duplicate some of the information in the package
-- database. We essentially keep two versions of the datbase in one file, one
-- version used only by ghc-pkg which keeps the full information (using the
-- serialised form of the 'InstalledPackageInfo' type defined by the Cabal
-- library); and a second version written by ghc-pkg and read by GHC which has
-- just the subset of information that GHC needs.
--
-- The second trick is that this module only defines in detail the format of
-- the second version -- the bit GHC uses -- and the part managed by ghc-pkg
-- is kept in the file but here we treat it as an opaque blob of data. That way
-- this library avoids depending on Cabal.
--
module GHC.PackageDb (
       InstalledPackageInfo(..),
       InstalledUnitInfo(..),
       ExposedModule(..),
       OriginalModule(..),
       BinaryStringRep(..),
       emptyInstalledPackageInfo,
       emptyInstalledUnitInfo,
       readPackageDbForGhc,
       readPackageDbForGhcPkg,
       writePackageDb
  ) where

import Data.Version (Version(..))
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS.Char8
import qualified Data.ByteString.Lazy as BS.Lazy
import qualified Data.ByteString.Lazy.Internal as BS.Lazy (defaultChunkSize)
import Data.Binary as Bin
import Data.Binary.Put as Bin
import Data.Binary.Get as Bin
import Control.Exception as Exception
import Control.Monad (when)
import System.FilePath
import System.IO
import System.IO.Error
import GHC.IO.Exception (IOErrorType(InappropriateType))
import System.Directory

type BinaryStringRep2 a b
    = (BinaryStringRep a, BinaryStringRep b)

type BinaryStringRep4 a b c d
    = (BinaryStringRep a, BinaryStringRep b,
       BinaryStringRep c, BinaryStringRep d)

type BinaryStringRep8 a b c d e f g h
    = (BinaryStringRep a, BinaryStringRep b,
       BinaryStringRep c, BinaryStringRep d,
       BinaryStringRep e, BinaryStringRep f,
       BinaryStringRep g, BinaryStringRep h)

-- TODO: rename pkgkey to unitkey

-- | A unit is a unit of modularity: it is a bundle of modules
-- (interfaces, code, and settings for how to link the code in.)
-- Traditionally, there was only one unit per package, but in Backpack
-- settings it's handy to have multiple units per package (e.g.
-- shipping a Backpack file with multiple units in it, or instantiating
-- a package multiple times with different parameters.)
data InstalledUnitInfo instpkgid instunitid unitname pkgkey modulename
   = InstalledUnitInfo {
       unitName           :: unitname,
       installedUnitId    :: instunitid,
       parentPackageId    :: instpkgid,
       packageKey         :: pkgkey,
       unitDepends        :: [instunitid],
       importDirs         :: [FilePath],
       hsLibraries        :: [String],
       exposedModules     :: [ExposedModule instunitid modulename],
       hiddenModules      :: [modulename],
       instantiatedWith   :: [(modulename,
                               OriginalModule instunitid modulename)]
    }
  deriving (Eq, Show)


-- | A package is a unit of distribution that may be uploaded to Hackage.
-- A package has no code per-se; rather, it contains a number of units.
-- This is a subset of Cabal's 'InstalledPackageInfo'.  GHC would ordinarily
-- not interact with packages at all, but it can be helpful for error
-- messages and backwards compatibility.
--
data InstalledPackageInfo instpkgid instunitid srcpkgid srcpkgname
                          unitname pkgkey versionhash modulename
   = InstalledPackageInfo {
       installedPackageId :: instpkgid,
       sourcePackageId    :: srcpkgid,
       packageName        :: srcpkgname,
       packageVersion     :: Version,
       versionHash        :: versionhash,
       units              :: [InstalledUnitInfo instpkgid instunitid unitname pkgkey modulename],
       extraLibraries     :: [String],
       extraGHCiLibraries :: [String],
       libraryDirs        :: [FilePath],
       frameworks         :: [String],
       frameworkDirs      :: [FilePath],
       ldOptions          :: [String],
       ccOptions          :: [String],
       includes           :: [String],
       includeDirs        :: [FilePath],
       haddockInterfaces  :: [FilePath],
       haddockHTMLs       :: [FilePath],
       exposed            :: Bool,
       trusted            :: Bool
     }
  deriving (Eq, Show)

-- | An original module is a fully-qualified module name (installed package ID
-- plus module name) representing where a module was *originally* defined
-- (i.e., the 'exposedReexport' field of the original ExposedModule entry should
-- be 'Nothing').  Invariant: an OriginalModule never points to a reexport.
data OriginalModule instunitid modulename
   = OriginalModule {
       originalInstalledUnitId :: instunitid,
       originalModuleName :: modulename
     }
  deriving (Eq, Show)

-- | Represents a module name which is exported by a package, stored in the
-- 'exposedModules' field.  A module export may be a reexport (in which
-- case 'exposedReexport' is filled in with the original source of the module),
-- and may be a signature (in which case 'exposedSignature is filled in with
-- what the signature was compiled against).  Thus:
--
--  * @ExposedModule n Nothing Nothing@ represents an exposed module @n@ which
--    was defined in this package.
--
--  * @ExposedModule n (Just o) Nothing@ represents a reexported module @n@
--    which was originally defined in @o@.
--
--  * @ExposedModule n Nothing (Just s)@ represents an exposed signature @n@
--    which was compiled against the implementation @s@.
--
--  * @ExposedModule n (Just o) (Just s)@ represents a reexported signature
--    which was originally defined in @o@ and was compiled against the
--    implementation @s@.
--
-- We use two 'Maybe' data types instead of an ADT with four branches or
-- four fields because this representation allows us to treat
-- reexports/signatures uniformly.
data ExposedModule instunitid modulename
   = ExposedModule {
       exposedName      :: modulename,
       exposedReexport  :: Maybe (OriginalModule instunitid modulename),
       exposedSignature :: Maybe (OriginalModule instunitid modulename)
     }
  deriving (Eq, Show)

class BinaryStringRep a where
  fromStringRep :: BS.ByteString -> a
  toStringRep   :: a -> BS.ByteString

emptyInstalledUnitInfo :: BinaryStringRep4 a b c d
                       => InstalledUnitInfo instpkgid a b c d
emptyInstalledUnitInfo =
  InstalledUnitInfo {
       unitName           = fromStringRep BS.empty,
       installedUnitId    = fromStringRep BS.empty,
       parentPackageId    = error "unknown parent package ID",
       packageKey         = fromStringRep BS.empty,
       unitDepends        = [],
       importDirs         = [],
       hsLibraries        = [],
       exposedModules     = [],
       hiddenModules      = [],
       instantiatedWith   = []
  }

emptyInstalledPackageInfo :: BinaryStringRep8 a b c d e f g h
                          => InstalledPackageInfo a b c d e f g h
emptyInstalledPackageInfo =
  InstalledPackageInfo {
       installedPackageId = fromStringRep BS.empty,
       sourcePackageId    = fromStringRep BS.empty,
       packageName        = fromStringRep BS.empty,
       packageVersion     = Version [] [],
       versionHash        = fromStringRep BS.empty,
       units              = [],
       extraLibraries     = [],
       extraGHCiLibraries = [],
       libraryDirs        = [],
       frameworks         = [],
       frameworkDirs      = [],
       ldOptions          = [],
       ccOptions          = [],
       includes           = [],
       includeDirs        = [],
       haddockInterfaces  = [],
       haddockHTMLs       = [],
       exposed            = False,
       trusted            = False
  }

-- | Read the part of the package DB that GHC is interested in.
--
readPackageDbForGhc :: BinaryStringRep8 a b c d e f g h =>
                       FilePath -> IO [InstalledPackageInfo a b c d e f g h]
readPackageDbForGhc file =
    decodeFromFile file getDbForGhc
  where
    getDbForGhc = do
      _version    <- getHeader
      _ghcPartLen <- get :: Get Word32
      ghcPart     <- get
      -- the next part is for ghc-pkg, but we stop here.
      return ghcPart

-- | Read the part of the package DB that ghc-pkg is interested in
--
-- Note that the Binary instance for ghc-pkg's representation of packages
-- is not defined in this package. This is because ghc-pkg uses Cabal types
-- (and Binary instances for these) which this package does not depend on.
--
readPackageDbForGhcPkg :: Binary pkgs => FilePath -> IO pkgs
readPackageDbForGhcPkg file =
    decodeFromFile file getDbForGhcPkg
  where
    getDbForGhcPkg = do
      _version    <- getHeader
      -- skip over the ghc part
      ghcPartLen  <- get :: Get Word32
      _ghcPart    <- skip (fromIntegral ghcPartLen)
      -- the next part is for ghc-pkg
      ghcPkgPart  <- get
      return ghcPkgPart

-- | Write the whole of the package DB, both parts.
--
writePackageDb :: (Binary pkgs, BinaryStringRep8 a b c d e f g h) =>
                  FilePath -> [InstalledPackageInfo a b c d e f g h] ->
                  pkgs -> IO ()
writePackageDb file ghcPkgs ghcPkgPart =
    writeFileAtomic file (runPut putDbForGhcPkg)
  where
    putDbForGhcPkg = do
        putHeader
        put               ghcPartLen
        putLazyByteString ghcPart
        put               ghcPkgPart
      where
        ghcPartLen :: Word32
        ghcPartLen = fromIntegral (BS.Lazy.length ghcPart)
        ghcPart    = encode ghcPkgs

getHeader :: Get (Word32, Word32)
getHeader = do
    magic <- getByteString (BS.length headerMagic)
    when (magic /= headerMagic) $
      fail "not a ghc-pkg db file, wrong file magic number"

    majorVersion <- get :: Get Word32
    -- The major version is for incompatible changes

    minorVersion <- get :: Get Word32
    -- The minor version is for compatible extensions

    when (majorVersion /= 2) $
      fail "unsupported ghc-pkg db format version"
    -- If we ever support multiple major versions then we'll have to change
    -- this code

    -- The header can be extended without incrementing the major version,
    -- we ignore fields we don't know about (currently all).
    headerExtraLen <- get :: Get Word32
    skip (fromIntegral headerExtraLen)

    return (majorVersion, minorVersion)

putHeader :: Put
putHeader = do
    putByteString headerMagic
    put majorVersion
    put minorVersion
    put headerExtraLen
  where
    majorVersion   = 2 :: Word32
    minorVersion   = 0 :: Word32
    headerExtraLen = 0 :: Word32

headerMagic :: BS.ByteString
headerMagic = BS.Char8.pack "\0ghcpkg\0"


-- TODO: we may be able to replace the following with utils from the binary
-- package in future.

-- | Feed a 'Get' decoder with data chunks from a file.
--
decodeFromFile :: FilePath -> Get a -> IO a
decodeFromFile file decoder =
    withBinaryFile file ReadMode $ \hnd ->
      feed hnd (runGetIncremental decoder)
  where
    feed hnd (Partial k)  = do chunk <- BS.hGet hnd BS.Lazy.defaultChunkSize
                               if BS.null chunk
                                 then feed hnd (k Nothing)
                                 else feed hnd (k (Just chunk))
    feed _ (Done _ _ res) = return res
    feed _ (Fail _ _ msg) = ioError err
      where
        err = mkIOError InappropriateType loc Nothing (Just file)
              `ioeSetErrorString` msg
        loc = "GHC.PackageDb.readPackageDb"

-- Copied from Cabal's Distribution.Simple.Utils.
writeFileAtomic :: FilePath -> BS.Lazy.ByteString -> IO ()
writeFileAtomic targetPath content = do
  let (targetDir, targetFile) = splitFileName targetPath
  Exception.bracketOnError
    (openBinaryTempFileWithDefaultPermissions targetDir $ targetFile <.> "tmp")
    (\(tmpPath, handle) -> hClose handle >> removeFile tmpPath)
    (\(tmpPath, handle) -> do
        BS.Lazy.hPut handle content
        hClose handle
        renameFile tmpPath targetPath)

instance BinaryStringRep4 a b c d =>
         Binary (InstalledUnitInfo instpkgid a b c d) where
  put (InstalledUnitInfo
         unitName installedUnitId _parentPackageId packageKey
         unitDepends importDirs
         hsLibraries
         exposedModules hiddenModules instantiatedWith) = do
    put (toStringRep unitName)
    put (toStringRep installedUnitId)
    put (toStringRep packageKey)
    put (map toStringRep unitDepends)
    put importDirs
    put hsLibraries
    put exposedModules
    put (map toStringRep hiddenModules)
    put (map (\(k,v) -> (toStringRep k, v)) instantiatedWith)
  get = do
    unitName           <- get
    installedUnitId    <- get
    packageKey         <- get
    unitDepends        <- get
    importDirs         <- get
    hsLibraries        <- get
    exposedModules     <- get
    hiddenModules      <- get
    instantiatedWith   <- get
    return (InstalledUnitInfo
              (fromStringRep unitName)
              (fromStringRep installedUnitId)
              (error "parentPackageId not filled in")
              (fromStringRep packageKey)
              (map fromStringRep unitDepends)
              importDirs
              hsLibraries
              exposedModules
              (map fromStringRep hiddenModules)
              (map (\(k,v) -> (fromStringRep k, v)) instantiatedWith))

instance BinaryStringRep8 a b c d e f g h =>
         Binary (InstalledPackageInfo a b c d e f g h) where
  put (InstalledPackageInfo
         installedPackageId sourcePackageId
         packageName packageVersion versionHash units
         extraLibraries extraGHCiLibraries libraryDirs
         frameworks frameworkDirs
         ldOptions ccOptions
         includes includeDirs
         haddockInterfaces haddockHTMLs
         exposed trusted) = do
    put (toStringRep installedPackageId)
    put (toStringRep sourcePackageId)
    put (toStringRep packageName)
    put packageVersion
    put (toStringRep versionHash)
    put units
    put extraLibraries
    put extraGHCiLibraries
    put libraryDirs
    put frameworks
    put frameworkDirs
    put ldOptions
    put ccOptions
    put includes
    put includeDirs
    put haddockInterfaces
    put haddockHTMLs
    put exposed
    put trusted

  get = do
    installedPackageId <- get
    sourcePackageId    <- get
    packageName        <- get
    packageVersion     <- get
    versionHash        <- get
    units              <- get
    extraLibraries     <- get
    extraGHCiLibraries <- get
    libraryDirs        <- get
    frameworks         <- get
    frameworkDirs      <- get
    ldOptions          <- get
    ccOptions          <- get
    includes           <- get
    includeDirs        <- get
    haddockInterfaces  <- get
    haddockHTMLs       <- get
    exposed            <- get
    trusted            <- get
    return (InstalledPackageInfo
              (fromStringRep installedPackageId)
              (fromStringRep sourcePackageId)
              (fromStringRep packageName)
              packageVersion
              (fromStringRep versionHash)
              -- fill in the parentPackageId
              (map (\u -> u { parentPackageId = fromStringRep installedPackageId })
                   units)
               extraLibraries extraGHCiLibraries libraryDirs
              frameworks frameworkDirs
              ldOptions ccOptions
              includes includeDirs
              haddockInterfaces haddockHTMLs
              exposed trusted)

instance Binary Version where
  put (Version a b) = do
    put a
    put b
  get = do
    a <- get
    b <- get
    return (Version a b)

instance BinaryStringRep2 a b => Binary (OriginalModule a b) where
  put (OriginalModule originalPackageId originalModuleName) = do
    put (toStringRep originalPackageId)
    put (toStringRep originalModuleName)
  get = do
    originalPackageId <- get
    originalModuleName <- get
    return (OriginalModule (fromStringRep originalPackageId)
                           (fromStringRep originalModuleName))

instance BinaryStringRep2 a b => Binary (ExposedModule a b) where
  put (ExposedModule exposedName exposedReexport exposedSignature) = do
    put (toStringRep exposedName)
    put exposedReexport
    put exposedSignature
  get = do
    exposedName <- get
    exposedReexport <- get
    exposedSignature <- get
    return (ExposedModule (fromStringRep exposedName)
                          exposedReexport
                          exposedSignature)
