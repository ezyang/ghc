{-# OPTIONS -fno-warn-incomplete-patterns -optc-DNON_POSIX_SOURCE #-}

-----------------------------------------------------------------------------
--
-- GHC Driver program
--
-- (c) The University of Glasgow 2005
--
-----------------------------------------------------------------------------

module Main (main) where

-- The official GHC API
import qualified GHC
import GHC		( -- DynFlags(..), HscTarget(..),
                          -- GhcMode(..), GhcLink(..),
                          Ghc, GhcMonad(..),
			  LoadHowMuch(..) )
import CmdLineParser

-- Implementations of the various modes (--show-iface, mkdependHS. etc.)
import LoadIface	( showIface )
import HscMain          ( newHscEnv )
import DriverPipeline	( oneShot, compileFile )
import DriverMkDepend	( doMkDependHS )
#ifdef GHCI
import InteractiveUI	( interactiveUI, ghciWelcomeMsg )
#endif


-- Various other random stuff that we need
import Config
import HscTypes
import Packages		( dumpPackages )
import DriverPhases	( Phase(..), isSourceFilename, anyHsc,
			  startPhase, isHaskellSrcFilename )
import BasicTypes       ( failed )
import StaticFlags
import StaticFlagParser
import DynFlags
import ErrUtils
import FastString
import Outputable
import SrcLoc
import Util
import Panic
import MonadUtils       ( liftIO )

-- Imports for --abi-hash
import LoadIface           ( loadUserInterface )
import Module              ( mkModuleName )
import Finder              ( findImportedModule, cannotFindInterface )
import TcRnMonad           ( initIfaceCheck )
import Binary              ( openBinMem, put_, fingerprintBinMem )

-- Standard Haskell libraries
import System.IO
import Foreign.C
import Foreign
import System.Environment hiding (getProgName)
import System.Exit
import System.FilePath
import Control.Monad
import Data.Char
import Data.List
import Data.Maybe

-----------------------------------------------------------------------------
-- ToDo:

-- time commands when run with -v
-- user ways
-- Win32 support: proper signal handling
-- reading the package configuration file is too slow
-- -K<size>

-----------------------------------------------------------------------------
-- GHC's command-line interface

getProgName :: IO String
getProgName =
  alloca $ \ p_argc ->
  alloca $ \ p_argv -> do
     getProgArgv p_argc p_argv
     argv <- peek p_argv
     unpackProgName argv

unpackProgName  :: Ptr (Ptr CChar) -> IO String   -- argv[0]
unpackProgName argv = do
  s <- peekElemOff argv 0 >>= peekCString
  return (basename s)
  where
   basename :: String -> String
   basename f = go f f
    where
      go acc [] = acc
      go acc (x:xs)
        | isPathSeparator x = go xs xs
        | otherwise         = go acc xs

   isPathSeparator :: Char -> Bool
   isPathSeparator '/'  = True
   isPathSeparator _    = False

foreign import ccall unsafe "getProgArgv"
  getProgArgv :: Ptr CInt -> Ptr (Ptr CString) -> IO ()

main :: IO ()
main = do

   s <- getProgName
   print s
   panic "asdf"
