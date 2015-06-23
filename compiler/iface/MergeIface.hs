{-# LANGUAGE CPP #-}
module MergeIface(mergeModIface, mergeModIface', mergeAvails) where

#include "HsVersions.h"

import Outputable
import HscTypes
import Module
import UniqFM
import Maybes
import Avail
import Name
import IfaceSyn

import HsSyn
import RnNames
import NameEnv
import Util
import Fingerprint

import Data.Either

{-
************************************************************************
*                                                                      *
                        Merging ModIfaces
*                                                                      *
************************************************************************
-}

-- NOTICE: this is DIRECTED. iface1 is the iface we are ACCUMULATING
mergeModIface' :: [(Fingerprint, IfaceDecl)] -> ModIface -> ModIface -> ModIface
mergeModIface' merged_decls iface1 iface2 =
    ASSERT2( mi_semantic_module iface1 == mi_semantic_module iface2
           , ppr (mi_top_module iface1) $$ ppr (mi_top_module iface2))
    let fixities = mergeFixities (mi_fixities iface1) (mi_fixities iface2)
        warns = mergeWarnings (mi_warns iface1) (mi_warns iface2)
        top_mod = mi_top_module iface1
    in (emptyModIface top_mod) { -- TODO mi_module here is bogus
        mi_hsc_src   = HsBootMerge,

        -- The merge proper
        mi_decls     = merged_decls,
        mi_anns      = mi_anns iface1 ++ mi_anns iface2,
        -- TODO filter out duplicates
        mi_exports   = mergeAvails (mi_exports iface1) (mi_exports iface2),
        mi_insts     = mi_insts iface1 ++ mi_insts iface2,
        mi_fam_insts = mi_fam_insts iface1 ++ mi_fam_insts iface2,
        mi_rules     = mi_rules iface1 ++ mi_rules iface2,

        -- Some harmless things which are easy to compute
        mi_orphan = mi_orphan iface1 || mi_orphan iface2,
        mi_finsts = mi_finsts iface1 || mi_finsts iface2,
        mi_used_th = mi_used_th iface1 || mi_used_th iface2,

        -- The key things
        mi_fixities = fixities,
        mi_warns = warns,
        mi_fix_fn = mkIfaceFixCache fixities,
        mi_warn_fn = mkIfaceWarnCache warns,
        mi_hash_fn = \n -> case mi_hash_fn iface1 n of
                            Nothing -> mi_hash_fn iface2 n
                            Just r -> Just r,

        -- Stuff we can stub out so we fail fast (had to be non-strict)
        mi_deps      = if moduleUnitKey (mi_module iface2) ==
                          moduleUnitKey (mi_module iface1)
                       then
                        (mi_deps iface1) {
                            dep_mods = (moduleName (mi_module iface2), mi_boot iface2)
                                     : dep_mods (mi_deps iface1)
                        }
                       else
                       -- TODO: more fine grained
                        (mi_deps iface1) {
                            dep_pkgs = (moduleUnitKey (mi_module iface2), False)
                                     : dep_pkgs (mi_deps iface1)
                        },
        mi_usages    = []
    }

-- MaybeErr is a bad warning because we want to report as
-- many errors as possible
-- TODO totally unclear what fingerprints should be, so omitted for now
mergeIfaceDecls :: [IfaceDecl]
                -> [IfaceDecl]
                -> MaybeErr
                    -- on error, we want to report the two IfaceDecls
                    -- for pretty printing, as well as a little description
                    -- why they were different.
                    [(IfaceDecl, IfaceDecl, SDoc)]
                    [IfaceDecl]
mergeIfaceDecls ds1 ds2 =
    let mkE ds = listToUFM [ (ifName d, d) | d <- ds ]
        (bad, ok) = partitionEithers
                  . map (\(d1,d2) -> case mergeIfaceDecl d1 d2 of
                                        Succeeded d -> Right d
                                        Failed err -> Left (d1, d2, err))
                  . eltsUFM
                  $ intersectUFM_C (,) (mkE ds1) (mkE ds2)
    in case bad of
              -- HACK using right bias
        [] -> Succeeded (eltsUFM (plusUFM (mkE ds1) (plusUFM (mkE ds2) (mkE ok))))
        _ -> Failed bad

mergeModIface :: ModIface -> ModIface -> MaybeErr [(IfaceDecl, IfaceDecl, SDoc)] ModIface
mergeModIface iface1 iface2 = do
    merged_decls <- fmap (map ((,) fingerprint0))
                  $ mergeIfaceDecls (map snd (mi_decls iface1))
                               (map snd (mi_decls iface2))
    let iface = mergeModIface' merged_decls iface1 iface2
    {- pprTrace "iface" (pprModIface iface) $ -}
    return iface

mergeFixities :: [(OccName, Fixity)] -> [(OccName, Fixity)] -> [(OccName, Fixity)]
mergeFixities fix1 fix2 =
    let forceEqual x y | x == y = x
                       | otherwise = panic "mergeFixities"
    in mergeOccList forceEqual fix1 fix2

mergeOccList :: ((OccName, a) -> (OccName, a) -> (OccName, a))
             -> [(OccName, a)] -> [(OccName, a)] -> [(OccName, a)]
mergeOccList f xs1 xs2 =
    let oe1 = mkOccEnv [ (fst x, x) | x <- xs1 ]
        oe2 = mkOccEnv [ (fst x, x) | x <- xs2 ]
    in occEnvElts (plusOccEnv_C f oe1 oe2)

-- TODO: better merging
mergeWarnings :: Warnings -> Warnings -> Warnings
mergeWarnings w@WarnAll{} _ = w
mergeWarnings _ w@WarnAll{} = w
mergeWarnings (WarnSome ws1) (WarnSome ws2) = WarnSome (mergeOccList const ws1 ws2)
mergeWarnings w@WarnSome{} _ = w
mergeWarnings _ w@WarnSome{} = w
mergeWarnings NoWarnings NoWarnings = NoWarnings


-- Assumes the AvailInfos have already been unified
mergeAvails :: [AvailInfo] -> [AvailInfo] -> [AvailInfo]
mergeAvails as1 as2 =
    let mkNE as = mkNameEnv [(availName a, a) | a <- as]
    in nameEnvElts (plusNameEnv_C plusAvail (mkNE as1) (mkNE as2))
