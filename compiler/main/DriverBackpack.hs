module DriverBackpack(doBackpack) where

-- A bit goofy
import qualified GHC
import GHC              ( Ghc )

import BackpackParser
import Backpack
import Lexer

import PackageConfig
import Packages

import HscTypes
import StringBuffer
import FastString
import ErrUtils
import MonadUtils       ( liftIO )
import SrcLoc

import Control.Monad

-- ----------------------------------------------------------------------------
-- Run --backpack mode

doBackpack :: FilePath -> [String] -> Ghc ()
doBackpack src_filename pkgs = do
    dflags <- GHC.getSessionDynFlags
    buf <- liftIO $ hGetStringBuffer src_filename
    let loc = mkRealSrcLoc (mkFastString src_filename) 1 1
    let global_db = map (\pkg -> (packageName pkg, installedPackageId pkg))
                        (listPackageConfigMap dflags)
    case unP parsePackages (mkBackpackPState dflags buf loc) of
        PFailed span err ->
            liftIO $ throwOneError (mkPlainErrMsg dflags span err)
        POk _ bkp -> do
            pkg_env <- liftIO $ mkPackageEnv src_filename bkp global_db
            forM_ pkgs $ \name ->
                compileConcrete pkg_env (mkGeneralLocated "<command line>" (mkPackageName name))
            forM_ (pkg_exes pkg_env) $ \pkg ->
                compile' pkg_env pkg emptyHoleMap


