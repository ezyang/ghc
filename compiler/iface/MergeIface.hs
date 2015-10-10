{-# LANGUAGE CPP #-}
module MergeIface(mergeModIface', mergeAvails) where

#include "HsVersions.h"

import Outputable
import HscTypes
import Avail
import Name
import IfaceSyn

import HsSyn
import RnNames
import NameEnv
import Util
import Fingerprint

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
    {- This assert is good for Backpack, but not good for ad hoc -sig-of usage
    ASSERT2( mi_semantic_module iface1 == mi_semantic_module iface2
           , ppr (mi_top_module iface1) $$ ppr (mi_top_module iface2))
           -}
    let fixities = mergeFixities (mi_fixities iface1) (mi_fixities iface2)
        warns = mergeWarnings (mi_warns iface1) (mi_warns iface2)
        mod = mi_module iface1
    in (emptyModIface mod) { -- TODO identity module here is bogus
        mi_hsc_src   = HsigFile,

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

        -- TODO: THIS IS TOTALLY WRONG
        mi_deps = let deps1 = mi_deps iface1
                      deps2 = mi_deps iface2
                  in Deps {
                    -- TODO dedupe more efficiently
                    dep_mods = nubSort (dep_mods deps1 ++ dep_mods deps2),
                    dep_pkgs = nubSort (dep_pkgs deps1 ++ dep_pkgs deps2),
                    dep_orphs = nubSort (dep_orphs deps1 ++ dep_orphs deps2),
                    dep_finsts = nubSort (dep_finsts deps1 ++ dep_finsts deps2)
                  },
        {-
        mi_deps      = if moduleUnitId (mi_module iface2) ==
                          moduleUnitId (mi_module iface1)
                       then
                        (mi_deps iface1) {
                            dep_mods = (moduleName (mi_module iface2), mi_boot iface2)
                                     : dep_mods (mi_deps iface1)
                        }
                       else
                       -- TODO: more fine grained
                        (mi_deps iface1) {
                            dep_pkgs = (moduleUnitId (mi_module iface2), False)
                                     : dep_pkgs (mi_deps iface1)
                        },
                        -}
        -- TODO: THIS IS PRETTY BAD TOO
        mi_usages    = []
    }

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
