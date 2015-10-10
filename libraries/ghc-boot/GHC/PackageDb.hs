{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
       IndefiniteUnitId(..),
       GenModule(..),
       UnitIdModuleRep(..),
       hashUnitId,
       BinaryStringRep(..),
       emptyInstalledPackageInfo,
       readPackageDbForGhc,
       readPackageDbForGhcPkg,
       writePackageDb
  ) where

import Data.Version (Version(..))
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS.Char8
import qualified Data.ByteString.Lazy as BS.Lazy
import qualified Data.ByteString.Lazy.Internal as BS.Lazy (defaultChunkSize)
import qualified Data.ByteString.Unsafe as BS
import Data.Binary as Bin
import Data.Binary.Put as Bin
import Data.Binary.Get as Bin
import qualified Data.Char as Char
import Numeric
import Control.Exception as Exception
import Control.Monad (when)
import Foreign.Ptr (castPtr)
import System.FilePath
import System.IO
import System.IO.Error
import System.IO.Unsafe (unsafePerformIO)
import GHC.IO.Exception (IOErrorType(InappropriateType))
import GHC.Fingerprint
import System.Directory

--------------------------------------------------------------------------
-- Base 62

-- The base-62 code is based off of 'locators'
-- ((c) Operational Dynamics Consulting, BSD3 licensed)

-- | Size of a 64-bit word when written as a base-62 string
word64Base62Len :: Int
word64Base62Len = 11

-- | Converts a 64-bit word into a base-62 string
toBase62Padded :: Word64 -> String
toBase62Padded w = pad ++ str
  where
    pad = replicate len '0'
    len = word64Base62Len - length str -- 11 == ceil(64 / lg 62)
    str = toBase62 w

toBase62 :: Word64 -> String
toBase62 w = showIntAtBase 62 represent w ""
  where
    represent :: Int -> Char
    represent x
        | x < 10 = Char.chr (48 + x)
        | x < 36 = Char.chr (65 + x - 10)
        | x < 62 = Char.chr (97 + x - 36)
        | otherwise = error "represent (base 62): impossible!"

hashUnitId :: (UnitIdModuleRep compid unitid modulename mod,
               BinaryStringRep compid, BinaryStringRep modulename)
         => compid -> [(modulename, mod)] -> BS.ByteString
hashUnitId cid sorted_holes
    -- Including empty
  | all (\(m, mod) -> BS.Char8.pack "hole" == unitIdHash (genModuleUnitId (toDbModule mod))
                   && toStringRep m == toStringRep (genModuleName (toDbModule mod))) sorted_holes =
    toStringRep cid
  | otherwise =
    fingerprintUnitId (toStringRep cid)
  . fingerprintByteString
  . BS.concat $ do
        (m, b_raw) <- sorted_holes
        let b = toDbModule b_raw
        [ toStringRep m,                BS.Char8.singleton ' ',
          unitIdHash (genModuleUnitId b), BS.Char8.singleton ':',
          toStringRep (genModuleName b),   BS.Char8.singleton '\n']

fingerprintByteString :: BS.ByteString -> Fingerprint
fingerprintByteString bs = unsafePerformIO
                         . BS.unsafeUseAsCStringLen bs
                         $ \(p,l) -> fingerprintData (castPtr p) l

fingerprintUnitId :: BS.ByteString -> Fingerprint -> BS.ByteString
fingerprintUnitId prefix (Fingerprint a b)
    = BS.concat
    $ [ prefix
      , BS.Char8.singleton '-'
      , BS.Char8.pack (toBase62Padded a)
      , BS.Char8.pack (toBase62Padded b) ]

-- | This is a subset of Cabal's 'InstalledPackageInfo', with just the bits
-- that GHC is interested in.
--
data InstalledPackageInfo compid srcpkgid srcpkgname unitid compname modulename mod
   = InstalledPackageInfo {
       sourcePackageId    :: srcpkgid,
       packageName        :: srcpkgname,
       packageVersion     :: Version,
       unitId             :: unitid,
       componentName      :: compname, -- "" means primary component
       abiHash            :: String,
       depends            :: [unitid],
       importDirs         :: [FilePath],
       hsLibraries        :: [String],
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
       exposedModules     :: [(modulename,mod)],
       hiddenModules      :: [modulename],
       instantiatedDepends:: [unitid],
       indefinite         :: Bool,
       exposed            :: Bool,
       trusted            :: Bool
     }
  deriving (Eq, Show)

type RepInstalledPackageInfo compid srcpkgid srcpkgname unitid compname modulename mod =
    (BinaryStringRep compid, BinaryStringRep srcpkgid,
     BinaryStringRep srcpkgname,
     BinaryStringRep compname, BinaryStringRep modulename,
     UnitIdModuleRep compid unitid modulename mod)

-- For consistency with Rep, we have a pile of phantom parameters on
-- GenModule/IndefiniteUnitId

-- | A Module is a pair of a 'UnitId' and a 'ModuleName'.
data GenModule compid unitid modulename mod = GenModule {
   genModuleUnitId :: unitid,
   genModuleName   :: modulename
  }
  deriving (Eq)
deriving instance (Show unitid, Show modulename)
                => Show (GenModule compid unitid modulename mod)

-- | An indefinite unit unitid is like an unit unitid, but with the full
-- information (e.g. what was instantiated) so that GHC can substitute
-- over it.
data IndefiniteUnitId compid unitid modulename mod
   = IndefiniteUnitId {
       indefUnitIdComponentId :: compid,
       indefUnitIdInsts :: [(modulename, mod)]
     }
  deriving (Eq)
deriving instance (Show compid, Show modulename, Show mod)
                => Show (IndefiniteUnitId compid unitid modulename mod)

class BinaryStringRep a where
  fromStringRep :: BS.ByteString -> a
  toStringRep   :: a -> BS.ByteString

-- Fundep is very important!

-- Can't generalize this to DbRep because the fundeps are very important
class UnitIdModuleRep compid unitid modulename mod | mod -> unitid, unitid -> mod, mod -> modulename , unitid -> compid where
  fromDbModule :: GenModule compid unitid modulename mod -> mod
  toDbModule :: mod -> GenModule compid unitid modulename mod
  fromDbUnitId :: IndefiniteUnitId compid unitid modulename mod -> unitid
  toDbUnitId :: unitid -> IndefiniteUnitId compid unitid modulename mod
  unitIdHash :: unitid -> BS.ByteString

emptyInstalledPackageInfo ::
    forall compid srcpkgid srcpkgname unitid compname modulename mod.
    RepInstalledPackageInfo compid srcpkgid srcpkgname unitid compname modulename mod
    => InstalledPackageInfo compid srcpkgid srcpkgname unitid compname modulename mod
emptyInstalledPackageInfo =
  InstalledPackageInfo {
       sourcePackageId    = fromStringRep BS.empty,
       packageName        = fromStringRep BS.empty,
       packageVersion     = Version [] [],
       abiHash            = "",
       --  :: IndefiniteUnitId compid modulename
       unitId             = fromDbUnitId (IndefiniteUnitId (fromStringRep BS.empty) []),
       componentName      = fromStringRep BS.empty,
       depends            = [],
       importDirs         = [],
       hsLibraries        = [],
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
       exposedModules     = [],
       hiddenModules      = [],
       instantiatedDepends= [],
       indefinite         = False,
       exposed            = False,
       trusted            = False
  }

-- | Read the part of the package DB that GHC is interested in.
--
readPackageDbForGhc ::
    RepInstalledPackageInfo a b c d e f g
    => FilePath -> IO [InstalledPackageInfo a b c d e f g]
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
writePackageDb :: (Binary pkgs, RepInstalledPackageInfo a b c d e f g) =>
                  FilePath -> [InstalledPackageInfo a b c d e f g] -> pkgs -> IO ()
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

    when (majorVersion /= 1) $
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
    majorVersion   = 1 :: Word32
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

instance      RepInstalledPackageInfo a b c d e f g =>
         Binary (InstalledPackageInfo a b c d e f g) where
  put (InstalledPackageInfo
         sourcePackageId
         packageName packageVersion unitId componentName
         abiHash depends importDirs
         hsLibraries extraLibraries extraGHCiLibraries libraryDirs
         frameworks frameworkDirs
         ldOptions ccOptions
         includes includeDirs
         haddockInterfaces haddockHTMLs
         exposedModules hiddenModules
         instantiatedDepends indefinite
         exposed trusted) = do
    put (toStringRep sourcePackageId)
    put (toStringRep packageName)
    put packageVersion
    put (toDbUnitId unitId)
    put (toStringRep componentName)
    put abiHash
    put (map toDbUnitId depends)
    put importDirs
    put hsLibraries
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
    put (map (\(k,v) -> (toStringRep k, toDbModule v)) exposedModules)
    put (map toStringRep hiddenModules)
    put (map toDbUnitId instantiatedDepends)
    put indefinite
    put exposed
    put trusted

  -- get :: forall a b c d e f g. RepInstalledPackageInfo a b c d e f g => Get (InstalledPackageInfo a b c d e f g)
  get = do
    sourcePackageId    <- get
    packageName        <- get
    packageVersion     <- get
    unitId             <- get -- :: Get (IndefiniteUnitId a f)
    componentName      <- get
    abiHash            <- get
    depends            <- get
    importDirs         <- get
    hsLibraries        <- get
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
    exposedModules     <- get
    hiddenModules      <- get
    instantiatedDepends<- get
    indefinite         <- get
    exposed            <- get
    trusted            <- get
    return (InstalledPackageInfo
              (fromStringRep sourcePackageId)
              (fromStringRep packageName) packageVersion
              (fromDbUnitId unitId)
              (fromStringRep componentName)
              abiHash
              (map fromDbUnitId depends)
              importDirs
              hsLibraries extraLibraries extraGHCiLibraries libraryDirs
              frameworks frameworkDirs
              ldOptions ccOptions
              includes includeDirs
              haddockInterfaces haddockHTMLs
              (map (\(k,v) -> (fromStringRep k, fromDbModule v)) exposedModules)
              (map fromStringRep hiddenModules)
              (map fromDbUnitId instantiatedDepends)
              indefinite
              exposed trusted)


instance (BinaryStringRep compid, BinaryStringRep modulename, UnitIdModuleRep compid unitid modulename mod) =>
         Binary (IndefiniteUnitId compid unitid modulename mod) where
  put (IndefiniteUnitId compid insts) = do
    put (toStringRep compid)
    put (map (\(k,v) -> (toStringRep k, toDbModule v)) insts)
  get = do
    a <- get
    b <- get
    return (IndefiniteUnitId
                (fromStringRep a)
                (map (\(k,v) -> (fromStringRep k, fromDbModule v)) b))

instance -- RepGenModule a b c d =>
  (BinaryStringRep compid, BinaryStringRep modulename, UnitIdModuleRep compid unitid modulename mod) =>
    Binary (GenModule compid unitid modulename mod) where
  put (GenModule moduleUnitId moduleName) = do
    put (toDbUnitId moduleUnitId)
    put (toStringRep moduleName)
  -- get :: forall a b c d. Get (GenModule a b c d)
  get = do
    moduleUnitId <- get -- :: Get (IndefiniteUnitId a b c d)
    moduleName   <- get
    return (GenModule (fromDbUnitId moduleUnitId)
                      (fromStringRep moduleName))
