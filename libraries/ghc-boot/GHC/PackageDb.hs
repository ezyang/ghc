{-# LANGUAGE CPP #-}
{-# LANGUAGE StandaloneDeriving #-}
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
       -- IndefiniteUnitInfo(..),
       IndefiniteUnitId(..),
       GenModule(..),
       BinaryStringRep(..),
       hashUnitId,
       emptyInstalledPackageInfo,
       readPackageDbForGhc,
       readPackageDbForGhcPkg,
       writePackageDb
  ) where

import Data.Typeable
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

hashUnitId :: (BinaryStringRep compid, BinaryStringRep modulename, BinaryStringRep unitid)
         => compid -> [(modulename, GenModule unitid modulename)] -> unitid
hashUnitId cid sorted_holes
    -- Including empty
  | all (\(m, mod) -> BS.Char8.pack "hole" == toStringRep (moduleUnitId mod)
                   && toStringRep m == toStringRep (moduleName mod)) sorted_holes =
    fromStringRep (toStringRep cid)
  | otherwise =
    fingerprintUnitId (toStringRep cid)
  . fingerprintByteString
  . BS.concat $ do
        (m, b) <- sorted_holes
        [ toStringRep m,                BS.Char8.singleton ' ',
          toStringRep (moduleUnitId b), BS.Char8.singleton ':',
          toStringRep (moduleName b),   BS.Char8.singleton '\n']

fingerprintByteString :: BS.ByteString -> Fingerprint
fingerprintByteString bs = unsafePerformIO
                         . BS.unsafeUseAsCStringLen bs
                         $ \(p,l) -> fingerprintData (castPtr p) l

fingerprintUnitId :: BinaryStringRep unitid => BS.ByteString -> Fingerprint -> unitid
fingerprintUnitId prefix (Fingerprint a b)
    = fromStringRep
    . BS.concat
    $ [ prefix
      , BS.Char8.singleton '-'
      , BS.Char8.pack (toBase62Padded a)
      , BS.Char8.pack (toBase62Padded b) ]

-- | This is a subset of Cabal's 'InstalledPackageInfo', with just the bits
-- that GHC is interested in.
--
data InstalledPackageInfo compid srcpkgid srcpkgname unitid compname modulename
   = InstalledPackageInfo {
       componentId        :: compid,
       sourcePackageId    :: srcpkgid,
       packageName        :: srcpkgname,
       packageVersion     :: Version,
       unitId             :: unitid,
       componentName      :: compname,
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
       exposedModules     :: [(modulename,GenModule unitid modulename)],
       hiddenModules      :: [modulename],
       instantiatedDepends:: [unitid],
       unitIdMap          :: [(unitid,IndefiniteUnitId unitid compid modulename)],
       indefinite         :: Bool,
       exposed            :: Bool,
       trusted            :: Bool
     }
  deriving (Eq, Show)

-- | A Module is a pair of a 'UnitId' and a 'ModuleName'.
data GenModule unitid modname = Module {
   moduleUnitId :: !unitid,  -- pkg-1.0
   moduleName   :: !modname  -- A.B.C
  }
  deriving (Eq, Ord, Typeable)
deriving instance (Show unitid, Show modname)
                => Show (GenModule unitid modname)

-- | An indefinite unit unitid is like an unit unitid, but with the full
-- information (e.g. what was instantiated) so that GHC can substitute
-- over it.
data IndefiniteUnitId unitid compid modulename
   = IndefiniteUnitId {
       indefUnitIdComponentId :: compid,
       indefUnitIdInsts :: [(modulename,
                             GenModule unitid modulename)]
     }
  deriving (Eq)
deriving instance (Show unitid, Show compid, Show modulename)
                => Show (IndefiniteUnitId unitid compid modulename)

class BinaryStringRep a where
  fromStringRep :: BS.ByteString -> a
  toStringRep   :: a -> BS.ByteString

emptyInstalledPackageInfo :: (BinaryStringRep a, BinaryStringRep b,
                              BinaryStringRep c, BinaryStringRep d,
                              BinaryStringRep e)
                          => InstalledPackageInfo a b c d e f
emptyInstalledPackageInfo =
  InstalledPackageInfo {
       componentId = fromStringRep BS.empty,
       sourcePackageId    = fromStringRep BS.empty,
       packageName        = fromStringRep BS.empty,
       packageVersion     = Version [] [],
       abiHash            = "",
       unitId             = fromStringRep BS.empty,
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
       unitIdMap          = [],
       indefinite         = False,
       exposed            = False,
       trusted            = False
  }

-- | Read the part of the package DB that GHC is interested in.
--
readPackageDbForGhc :: (BinaryStringRep a, BinaryStringRep b, BinaryStringRep c,
                        BinaryStringRep d, BinaryStringRep e, BinaryStringRep f) =>
                       FilePath -> IO [InstalledPackageInfo a b c d e f]
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
writePackageDb :: (Binary pkgs, BinaryStringRep a, BinaryStringRep b,
                   BinaryStringRep c, BinaryStringRep d, BinaryStringRep e,
                   BinaryStringRep f) =>
                  FilePath -> [InstalledPackageInfo a b c d e f] -> pkgs -> IO ()
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

instance (BinaryStringRep a, BinaryStringRep b, BinaryStringRep c,
          BinaryStringRep d, BinaryStringRep e, BinaryStringRep f) =>
         Binary (InstalledPackageInfo a b c d e f) where
  put (InstalledPackageInfo
         componentId sourcePackageId
         packageName packageVersion unitId componentName
         abiHash depends importDirs
         hsLibraries extraLibraries extraGHCiLibraries libraryDirs
         frameworks frameworkDirs
         ldOptions ccOptions
         includes includeDirs
         haddockInterfaces haddockHTMLs
         exposedModules hiddenModules
         instantiatedDepends unitIdMap indefinite
         exposed trusted) = do
    put (toStringRep componentId)
    put (toStringRep sourcePackageId)
    put (toStringRep packageName)
    put packageVersion
    put (toStringRep unitId)
    put (toStringRep componentName)
    put abiHash
    put (map toStringRep depends)
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
    put (map (\(k,v) -> (toStringRep k, v)) exposedModules)
    put (map toStringRep hiddenModules)
    put (map toStringRep instantiatedDepends)
    put (map (\(k,v) -> (toStringRep k, v)) unitIdMap)
    put indefinite
    put exposed
    put trusted

  get = do
    componentId <- get
    sourcePackageId    <- get
    packageName        <- get
    packageVersion     <- get
    unitId             <- get
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
    unitIdMap          <- get
    indefinite         <- get
    exposed            <- get
    trusted            <- get
    return (InstalledPackageInfo
              (fromStringRep componentId)
              (fromStringRep sourcePackageId)
              (fromStringRep packageName) packageVersion
              (fromStringRep unitId)
              (fromStringRep componentName)
              abiHash
              (map fromStringRep depends)
              importDirs
              hsLibraries extraLibraries extraGHCiLibraries libraryDirs
              frameworks frameworkDirs
              ldOptions ccOptions
              includes includeDirs
              haddockInterfaces haddockHTMLs
              (map (\(k,v) -> (fromStringRep k, v)) exposedModules)
              (map fromStringRep hiddenModules)
              (map fromStringRep instantiatedDepends)
              (map (\(k,v) -> (fromStringRep k, v)) unitIdMap)
              indefinite
              exposed trusted)

instance Binary Version where
  put (Version a b) = do
    put a
    put b
  get = do
    a <- get
    b <- get
    return (Version a b)

instance (BinaryStringRep a, BinaryStringRep b, BinaryStringRep c) =>
         Binary (IndefiniteUnitId a b c) where
  put (IndefiniteUnitId compid insts) = do
    put (toStringRep compid)
    put (map (\(k,v) -> (toStringRep k, v)) insts)
  get = do
    a <- get
    b <- get
    return (IndefiniteUnitId (fromStringRep a) (map (\(k,v) -> (fromStringRep k, v)) b))

instance (BinaryStringRep a, BinaryStringRep b) =>
         Binary (GenModule a b) where
  put (Module moduleUnitId moduleName) = do
    put (toStringRep moduleUnitId)
    put (toStringRep moduleName)
  get = do
    moduleUnitId <- get
    moduleName <- get
    return (Module (fromStringRep moduleUnitId)
                   (fromStringRep moduleName))
