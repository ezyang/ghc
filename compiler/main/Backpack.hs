{-# LANGUAGE MultiWayIf, NondecreasingIndentation #-}

-- -----------------------------------------------------------------------------
--
-- This module implements multi-package compilation (i.e. Backpack), and is used
-- by --backpack.
--
-- -----------------------------------------------------------------------------
module Backpack where

import qualified GHC
import GHC (LoadHowMuch(..))
import GhcMonad

import GHC.PackageDb

import SrcLoc
import Outputable
import HscTypes
import BasicTypes
import Module
import FastString
import PackageConfig
import DynFlags
import Packages
import UniqFM
import Digraph
import Finder
import ErrUtils
import Maybes

import Data.IORef
import Data.Version
import System.Exit
import System.FilePath
import Control.Monad
import Data.List
import System.Directory
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Char as Char
import Numeric
import Data.Word
import GHC.Fingerprint
import Data.Ord

--------------------------------------------------------------------------
-- Backpack data type

-- | Source-level representation of a Backpack package; basically corresponds
-- directly to the key-value syntax.
data Backpack
    = Backpack {
        backpackName :: PackageName,
        backpackIncludes :: [LPkgInclude],
        backpackExposedModules :: [LModuleName],
        backpackSourceDir :: Maybe (Located FilePath),
        backpackExecutable :: Maybe (Located String),
        -- These are only valid when executable
        backpackOutputFile :: Maybe (Located FilePath),
        -- These are only valid when not an executable
        backpackOtherModules :: [LModuleName],
        backpackExposedSignatures :: [LModuleName],
        backpackRequiredSignatures :: [LModuleName],
        backpackReexportedModules :: [Located (ModuleName, ModuleName)]
        -- TODO: miscellaneous installed package fields
    }

data PkgInclude = PkgInclude {
        includeName :: PackageName,
        includeRenaming :: Maybe [Located (ModuleName, ModuleName)]
    }

emptyExecutable :: Backpack
emptyExecutable = emptyBackpack (mkPackageName "main")

emptyBackpack :: PackageName -> Backpack
emptyBackpack name = Backpack {
        backpackName = name,
        backpackIncludes = [],
        backpackExposedModules = [],
        backpackOtherModules = [],
        backpackExposedSignatures = [],
        backpackRequiredSignatures = [],
        backpackReexportedModules = [],
        backpackSourceDir = Nothing,
        backpackOutputFile = Nothing,
        backpackExecutable = Nothing
    }

type PackageType = Set ModuleName -- holes
type BackpackField = Backpack -> Backpack -- used by the lexer

type LModule = Located Module
type LModuleName = Located ModuleName
type LPackageName = Located PackageName
type LBackpack = Located Backpack
type LPkgInclude = Located PkgInclude

type HoleMap = Map ModuleName LModule
emptyHoleMap :: HoleMap
emptyHoleMap = Map.empty

--------------------------------------------------------------------------
-- PackageEnv

-- | Information about the Backpack packages that we know about.
data PackageEnv =
    PackageEnv {
          -- | Source package map from 'PackageName' to 'LBackpack'
          pkg_sources  :: UniqFM LBackpack
          -- | List of executables
        , pkg_exes :: [LBackpack]
          -- | Installed package map from 'PackageName' to
          -- 'InstalledPackageId'.  This map is disjoint from
          -- 'pkg_sources'.
        , pkg_installs :: UniqFM InstalledPackageId
          -- | Derived from 'pkg_sources', this is a map from
          -- 'PackageName' to the holes that a source package requires.
          -- This is a transitively defined property so it's convenient
          -- to pre-compute this before doing any operations.
        , pkg_types    :: UniqFM PackageType
          -- | File name of our Backpack file
        , pkg_bkp_file :: FilePath
          -- | Errors we have collected during this compilation.
          -- (Currently unused.)
        , pkg_messages :: {-# UNPACK #-} !(IORef Messages)
        }

lookupBackpack :: PackageEnv -> PackageName -> Maybe LBackpack
lookupBackpack pkg_env = lookupUFM (pkg_sources pkg_env)

-- | Given a 'PackageName', lookup what holes would need to be filled in
-- order to compile.  If we don't have a 'Backpack' for the package, this
-- always returns @Nothing@.
lookupHoles :: PackageEnv -> PackageName -> Maybe PackageType
lookupHoles pkg_env = lookupUFM (pkg_types pkg_env)

lookupInstalledPackage :: PackageEnv -> PackageName -> Maybe InstalledPackageId
lookupInstalledPackage pkg_env = lookupUFM (pkg_installs pkg_env)

mkPackageEnv :: FilePath -> [LBackpack] -> [(PackageName, InstalledPackageId)] -> IO PackageEnv
mkPackageEnv fn src_list installed_list = do
    let (libs, exes) = partition (isNothing . backpackExecutable . unLoc) src_list
        src_pkg_db = listToUFM . map (\x -> (backpackName (unLoc x), x)) $ libs
        installed_db = listToUFM installed_list
    messages_ref <- newIORef emptyMessages
    return PackageEnv {
        pkg_sources  = src_pkg_db,
        pkg_exes     = exes,
        pkg_installs = installed_db,
        pkg_types    = calculateHoles src_pkg_db,
        pkg_bkp_file = fn,
        pkg_messages = messages_ref
    }

--------------------------------------------------------------------------
-- Base 62

-- The base-62 code is based off of 'locators'
-- ((c) Operational Dynamics Consulting, BSD3 licensed)

-- Note: Instead of base-62 encoding a single 128-bit integer
-- (ceil(21.49) characters), we'll base-62 a pair of 64-bit integers
-- (2 * ceil(10.75) characters).  Luckily for us, it's the same number of
-- characters!  In the long term, this should go in GHC.Fingerprint,
-- but not now...

-- | Size of a 64-bit word when written as a base-62 string
word64Base62Len :: Int
word64Base62Len = 11

-- | Converts a 64-bit word into a base-62 string
toBase62 :: Word64 -> String
toBase62 w = pad ++ str
  where
    pad = replicate len '0'
    len = word64Base62Len - length str -- 11 == ceil(64 / lg 62)
    str = showIntAtBase 62 represent w ""
    represent :: Int -> Char
    represent x
        | x < 10 = Char.chr (48 + x)
        | x < 36 = Char.chr (65 + x - 10)
        | x < 62 = Char.chr (97 + x - 36)
        | otherwise = error ("represent (base 62): impossible!")

fingerprintPackageKey :: String -> Fingerprint -> PackageKey
fingerprintPackageKey s (Fingerprint a b) = stringToPackageKey (s ++ "_" ++ toBase62 a ++ toBase62 b)

--------------------------------------------------------------------------
-- Package key

-- TODO: The fact that the package key fingerprinting is done by assembling
-- a bunch of Strings is suboptimal.  Not sure what the best way of assembling
-- FastStrings is, however; might be worst.

packageKeyHash :: PackageKey -> String
packageKeyHash pk =
    let s = packageKeyString pk in
    case dropWhile (/='_') s of
        [] -> s
        (_:rest) -> rest

-- | Generates a 'PackageKey' from a 'PackageId', sorted package keys of the
-- immediate dependencies.
mkPackageKey :: PackageName
             -> SourcePackageId
--             -> [PackageKey]     -- dependencies
             -> [(ModuleName, Module)] -- hole instantiations
             -> PackageKey
mkPackageKey (PackageName fsName) (SourcePackageId fsSource) {- deps -} holes =
    fingerprintPackageKey stubName . fingerprintString $
        unpackFS fsSource ++ "\n" ++
        -- NB: packageKeyHash, NOT display
        concat [ moduleNameString m ++ " " ++ packageKeyHash (modulePackageKey b) ++ ":" ++ moduleNameString (moduleName b) ++ "\n"
               | (m, b) <- sortBy (comparing fst) holes] -- ++
        -- TODO: This algorithm results in package keys which don't distinguish
        -- between packages compiled against different versions of their
        -- dependencies.  But we can't just use the package keys of the includes
        -- because that will result in a circular problem; so the version hashes
        -- have to be supplied out of band.
{-
        concat [ packageKeyHash d ++ "\n"
               | d <- sortBy (comparing packageKeyHash) deps]
               -}
  where stubName = take 5 (filter (/= '-') (unpackFS fsName))

--------------------------------------------------------------------------
-- Utilities

overHscDynFlags :: (DynFlags -> DynFlags) -> HscEnv -> HscEnv
overHscDynFlags f hsc_env = hsc_env { hsc_dflags = f (hsc_dflags hsc_env) }

convOriginalModule :: DynFlags -> OriginalModule InstalledPackageId ModuleName -> Module
convOriginalModule dflags (OriginalModule a b) = mkModule (resolveInstalledPackageId dflags a) b

convRenaming :: Maybe [Located (ModuleName, ModuleName)] -> ModRenaming
convRenaming Nothing = ModRenaming True []
convRenaming (Just rns) = ModRenaming False [ (orig, new) | L _ (orig, new) <- rns]

--------------------------------------------------------------------------
-- Main

-- TODO: collect warnings and don't eagerly report them

-- | Topologically sort a list of 'LBackpack' descriptions, where edges
-- are induced by includes.
topsortPkgs :: [LBackpack] -> [LBackpack]
topsortPkgs = map (\(pkg, _, _) -> pkg)
            . topologicalSortG
            . graphFromEdgedVertices
            . map (\l@(L _ p) ->
                       (l, backpackName p,
                        map (includeName.unLoc) (backpackIncludes p)))

calculateHoles :: UniqFM LBackpack -> UniqFM (Set ModuleName)
calculateHoles src_pkg_db = foldl' add_trans emptyUFM
                                   (topsortPkgs (eltsUFM src_pkg_db))
  -- TODO: simplify this by doing a different stage first
  -- (Wait, what did I mean here? Probably in the sense of changing all
  -- of the various fields into some sort of uniform representation like
  -- how ghc-pkg exposed works now)
  where add_trans m (L _ pkg) = addToUFM m (backpackName pkg)
                            (Set.fromList (map unLoc (backpackRequiredSignatures pkg)
                                ++ map unLoc (backpackExposedSignatures pkg)
                                ++ concatMap (add_dep m) (backpackIncludes pkg)))
        add_dep m (L _ (PkgInclude n rns))
            | Just holes <- lookupUFM m n = conv_rn holes rns
            | otherwise                   = []
        conv_rn holes Nothing
            = Set.toList holes
        conv_rn holes (Just rns)
            = mapMaybe (\(L _ (orig,new)) -> if Set.member orig holes
                                                then Just new
                                                else Nothing) rns

-- | Compile a definite package, that is, a package which is guaranteed not
-- to have any holes.
compileConcrete :: PackageEnv -> Located PackageName -> Ghc PackageConfig
compileConcrete pkg_env name = compile pkg_env name Map.empty

compile :: PackageEnv
        -> Located PackageName
        -> HoleMap
        -> Ghc PackageConfig
compile pkg_env (L loc name) hmap
    | Just p <- lookupBackpack pkg_env name
    = compile' pkg_env p hmap
    -- We don't have information on the package, but maybe
    -- it's already installed.  Unfortunately GHC API doesn't give
    -- us a convenient way to query by package name so for now
    -- just hard code everything in
    | Just ipid <- lookupInstalledPackage pkg_env name
    = do dflags <- GHC.getSessionDynFlags
         return (getPackageDetails dflags (resolveInstalledPackageId dflags ipid))
    | otherwise
    = do dflags <- GHC.getSessionDynFlags
         liftIO $ throwOneError (noPackageError dflags loc name)

noPackageError :: DynFlags -> SrcSpan -> PackageName -> ErrMsg
noPackageError dflags loc name = mkPlainErrMsg dflags loc
                    (text "Could not find package" <+> quotes (ppr name))

addPackage :: PackageConfig -> Ghc ()
addPackage pkg = do
    dflags0 <- GHC.getSessionDynFlags
    case pkgDatabase dflags0 of
        Nothing -> panic "addPackage: called too early"
        Just pkgs -> do let dflags = dflags0 { pkgDatabase = Just (pkg : pkgs) }
                        _ <- GHC.setSessionDynFlags dflags
                        -- By this time, the global ref has probably already
                        -- been forced, in which case doing this isn't actually
                        -- going to do you any good.
                        -- dflags <- GHC.getSessionDynFlags
                        -- liftIO $ setUnsafeGlobalDynFlags dflags
                        return ()

-- TODO: Error messages can be greatly improved if we maintain a stack
-- of hole instantiations so we can report to the user WHY a particular
-- linkage happened (e.g. a list of relevant bindings)

compileDep :: PackageEnv
           -> (HoleMap, [(PackageConfig, LPkgInclude)])
           -> LPkgInclude
           -> Ghc (HoleMap, [(PackageConfig, LPkgInclude)])
compileDep pkg_env (m, pkgs) incl@(L toploc (PkgInclude n rns)) = do
  dflags <- GHC.getSessionDynFlags

  (pkg, sub_m) <- if
    | Just holes <- lookupHoles pkg_env n
      -> do let rename_hole :: HoleMap -> Located (ModuleName, ModuleName) -> Ghc HoleMap
                rename_hole m' (L loc (orig, new))
                  | Set.member orig holes =
                      case Map.lookup new m of
                          Just v -> return $ Map.insert orig v m'
                          Nothing -> liftIO $ throwOneError (mkPlainErrMsg dflags loc
                              (vcat [text "Could not find module" <+> quotes (ppr new)
                                    ,text "to instantiate hole" <+> quotes (ppr orig)
                                    <+> text "in package" <+> quotes (ppr n)]))
                  | otherwise = return m'
            sub_m <- case rns of
                      Nothing -> return (Map.intersection m (Map.fromSet (const ()) holes))
                      Just rns' -> foldM rename_hole Map.empty rns'
            r <- compile pkg_env (L toploc n) sub_m
            return (r, sub_m)
    | Just ipid <- lookupInstalledPackage pkg_env n
      -> return (getPackageDetails dflags (resolveInstalledPackageId dflags ipid), Map.empty)
    | otherwise
      -> liftIO $ throwOneError (noPackageError dflags toploc n)
  dflags <- GHC.getSessionDynFlags

  let add_pkg :: HoleMap
              -> Maybe [Located (ModuleName, ModuleName)]
              -> Ghc HoleMap
      add_pkg m Nothing = foldM (add_mod toploc) m
                        . map (\e@(ExposedModule n _ _) -> (n, e))
                        $ exposedModules pkg
      add_pkg m (Just rns) = foldM add_rn_mod m rns

      add_rn_mod :: HoleMap
                 -> Located (ModuleName, ModuleName)
                 -> Ghc HoleMap
      add_rn_mod m (L loc (orig, new)) =
          case find (\(ExposedModule n _ _) -> n == orig) (exposedModules pkg) of
              Nothing
                -- If it showed up in sub_m, then it's a required-signature:
                -- we needed the renaming to figure out how to instantiate
                -- the package, but we don't add it to the context
                | Map.member orig sub_m -> return m
                | otherwise ->
                  liftIO $ throwOneError (mkPlainErrMsg dflags loc
                                (text "Could not find module" <+> quotes (ppr orig) <+>
                                 text "in package" <+> quotes (ppr n)))
              Just e -> add_mod loc m (new, e)

      add_mod loc m (bnd, ExposedModule _ _ (Just backing))
          = add_mod' bnd (L loc (convOriginalModule dflags backing)) m
      add_mod loc m (bnd, ExposedModule _ (Just export) Nothing)
          = add_mod' bnd (L loc (convOriginalModule dflags export)) m
      add_mod loc m (bnd, ExposedModule n Nothing Nothing)
          = add_mod' bnd (L loc (mkModule (packageKey pkg) n)) m

      add_mod' bnd mod m
          | Just mod' <- Map.lookup bnd m
          , unLoc mod' /= unLoc mod
              = liftIO $ throwOneError (linkingError dflags bnd mod' mod)
          | otherwise
              = return $ Map.insert bnd mod m


  m' <- add_pkg m rns
  return (m', (pkg, incl):pkgs)

linkingError :: DynFlags
             -> ModuleName
             -> Located Module
             -> Located Module
             -> ErrMsg
linkingError dflags name old new = mkPlainErrMsg dflags (getLoc new) msg
    where msg = vcat [ text "Ambiguous module name" <+> quotes (ppr name)
                     , hang (text "It is being linked to" <+> quotes (ppr new))
                          2 (text "but it was previously" <+> quotes (ppr old) <+>
                             text "from" <+> quotes (ppr (getLoc old)))
                     ]

mkOriginalModule :: DynFlags -> InstalledPackageId -> Module -> OriginalModule InstalledPackageId ModuleName
mkOriginalModule dflags home_ipid mod =
  let ipid | modulePackageKey mod == thisPackage dflags = home_ipid
           | otherwise = installedPackageId $ getPackageDetails dflags (modulePackageKey mod)
  in OriginalModule ipid (moduleName mod)

-- Invariant: hmap contains only PRECISELY the holes you need.  This
-- means we can just slam it and make a package key
compile' :: PackageEnv -> LBackpack -> HoleMap -> Ghc PackageConfig
compile' pkg_env (L _ p) hmap = do
    let PackageName fs_name = backpackName p
        version = makeVersion [0] -- TODO Grab it from real field
        source_pkg_id = SourcePackageId fs_name -- TODO use version
        -- TODO generalize this for "executable" entries
        key | Just _ <- backpackExecutable p = mainPackageKey
            | otherwise =  mkPackageKey (backpackName p) source_pkg_id (Map.toList (fmap unLoc hmap))

    dflags <- GHC.getSessionDynFlags

    -- Short circuit if we've already compiled this one
    (\k -> case lookupPackage dflags key of
            Just p -> return p
            Nothing -> k) $ do

    -- Compile dependencies
    -- TODO: Discarding the hmap at the end is a bit goofy, since Packages
    -- is going to recalculate the moral equivalent of this; but there's no
    -- way to program the package state in this way (yet).
    (_, pkg_flags) <- foldM (compileDep pkg_env) (hmap, []) (backpackIncludes p)
    dflags <- GHC.getSessionDynFlags

    let showMsg msg = compilationProgressMsg dflags (showSDoc dflags msg)
        ppr_hole (n, L _ m)
          | not (qualModule defaultUserStyle m)
          , n == moduleName m = []
          | otherwise = [ppr n <+> text "as" <+> ppr m]
        hole_description
          | Map.null hmap = empty
          | otherwise = parens (sep (punctuate comma (concatMap ppr_hole (Map.toList hmap))))

    liftIO . showMsg $ case backpackExecutable p of
        Nothing -> blankLine $$ text "BUILDING package" <+> ppr (backpackName p) <+> brackets (ppr key) <> colon
        Just (L _ p) -> blankLine $$ text "BUILDING executable" <+> text p <> colon

    let basedir | Just (L _ dir) <- backpackSourceDir p = dir
                | Just (L _ fn) <- backpackOutputFile p = "out_" ++ fn
                | otherwise = "."
        outdir | Just f <- objectDir dflags = f </> packageKeyString key
               | Map.null hmap = basedir
               | otherwise = basedir </> "out_" ++ packageKeyString key
    liftIO $ createDirectoryIfMissing True outdir

    exe_target <- case backpackExecutable p of
        Nothing -> return []
        Just (L _ s) -> fmap (:[]) (GHC.guessTarget s Nothing)

    let targets = exe_target
               ++ map (\(L _ m) -> Target (TargetModule m) True Nothing)
                      (backpackExposedModules p)

    (ipid, exposed, obj_files) <- withTempSession (overHscDynFlags (\dflags -> 
      {- flip gopt_set Opt_HideAllPackages $ -} dflags {
        importPaths = maybeToList (fmap unLoc (backpackSourceDir p)),
        thisPackage = key,
        objectDir   = Just outdir,
        hiDir       = Just outdir,
        stubDir     = Just outdir,
        outputFile  = fmap unLoc (backpackOutputFile p),
        sigOf       = fmap unLoc hmap,
        -- Goofy conversion to string, related to the discarded hmap TODO
        packageFlags= [ ExposePackage (PackageIdArg (installedPackageIdString pkg))
                                      (convRenaming rns)
                      | (pkg, L _ (PkgInclude _ rns)) <- pkg_flags ],
        includePaths= outdir : includePaths dflags,
        dumpDir     = Just outdir
    })) $ do
        -- Well, this is silly!
        _ <- GHC.setSessionDynFlags =<< GHC.getSessionDynFlags
        dflags <- GHC.getSessionDynFlags

        GHC.setTargets targets
        ok_flag <- GHC.load LoadAllTargets
        when (failed ok_flag) (liftIO $ exitWith (ExitFailure 1))
        hsc_env <- getSession

        -- It IS important for this to be unique, because it's how we
        -- do look ups.
        let ipid = InstalledPackageId (packageKeyFS key)

        -- NB: you can't use the hmap, because it won't do signature visibility
        -- right.
        let lookup_reexport (L loc (m, n)) = do
              r <- liftIO $ findImportedModule hsc_env m Nothing
              case r of
                FoundModule fr ->
                  return [ExposedModule n (Just (mkOriginalModule dflags ipid (fr_mod fr)))
                                          Nothing]
                FoundSigs sigs orig ->
                  return (map (\fr ->
                    ExposedModule n (Just (mkOriginalModule dflags ipid (fr_mod fr)))
                                    (Just (mkOriginalModule dflags ipid orig))) sigs)
                _ -> liftIO $ throwOneError (mkPlainErrMsg dflags loc (text "Could not find module" <+> quotes (ppr m) <+> text "for reexport"))

        reexports <- fmap concat $ mapM lookup_reexport (backpackReexportedModules p)

        let lookup_sig (L _ m) =
              case Map.lookup m hmap of
                Nothing -> pprPanic "lookup_sig" (ppr m $$ ppr hmap)
                Just (L _ orig) ->
                  ExposedModule m Nothing (Just (mkOriginalModule dflags ipid orig))
            sigs = map lookup_sig (backpackExposedSignatures p)

        let exposed :: [ExposedModule InstalledPackageId ModuleName]
            exposed = map (\n -> ExposedModule (unLoc n) Nothing Nothing)
                          (backpackExposedModules p)
                            ++ sigs ++ reexports

        -- We also need to figure out object files (copied from DriverPipeline)
        hsc_env <- getSession

        let home_mod_infos = eltsUFM (hsc_HPT hsc_env)
            linkables = map (expectJust "link".hm_linkable) home_mod_infos
            getOfiles (LM _ _ us) = map nameOfObject (filter isObject us)
            obj_files = concatMap getOfiles linkables

        liftIO $ flushFinderCaches hsc_env

        return (ipid, exposed, obj_files)

    let pkg = InstalledPackageInfo {
            installedPackageId = ipid,
            sourcePackageId = source_pkg_id,
            packageName = backpackName p,
            packageVersion = version,
            packageKey = key,
            exposedModules = exposed,
            hiddenModules = [], -- TODO: doc only
            instantiatedWith = [], -- TODO (not used by anything right now)
            depends = [ installedPackageId pkg | (pkg, _) <- pkg_flags ],
            -- We're too lazy to make 'ar' archives, so instead just slam
            -- all the object files in the database
            ldOptions = obj_files,
            importDirs = [ outdir ],
            exposed = False,
            -- nope
            hsLibraries = [],
            extraLibraries = [],
            extraGHCiLibraries = [],
            libraryDirs = [],
            frameworks = [],
            frameworkDirs = [],
            ccOptions = [],
            includes = [],
            includeDirs = [],
            haddockInterfaces = [],
            haddockHTMLs = [],
            trusted = False
        }
    when (isNothing (backpackExecutable p)) $ addPackage pkg
    return pkg

-- Possible optimization: when I finish compiling a home package, I can transfer
-- it DIRECTLY to the external package state.  It's a bit delicate
-- though.
