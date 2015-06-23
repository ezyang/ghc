{-# LANGUAGE CPP #-}
module Shape(
    -- * Shape data types
    ShProvides, ShRequires,
    ModShape(..), AvailShape(..), Shape(..),
    emptyModShape, emptyAvailShape, emptyShape,
    shapeProvides, shapeRequires,
    ) where

#include "HsVersions.h"

import Outputable
import Module
import Avail
import Util

import Data.Map (Map)
import qualified Data.Map as Map

{-
************************************************************************
*                                                                      *
                        Shapes
*                                                                      *
************************************************************************
-}

-- | A map from module name to the 'Module' identity which provides it.
type ShProvides = Map ModuleName Module

-- | A map from module name to the outer 'Module' identities of the signatures
-- which specify our requirements for it.  Each 'Module' in @['Module']@ is of
-- the form @p(A -> HOLE:A):A@ instead of @HOLE:A@: this lets us identify the
-- specific hsig file associated with the signature.
type ShRequires = Map ModuleName [Module]

data ModShape = ModShape {
        sh_mod_provides :: ShProvides,
        sh_mod_requires :: ShRequires
    }

data AvailShape = AvailShape {
        sh_avail_provides :: Map ModuleName [AvailInfo],
        sh_avail_requires :: Map ModuleName [AvailInfo]
    }

data Shape = Shape ModShape AvailShape

instance Outputable Shape where
    ppr sh =
        hang (text "provides:") 10
              (vcat [ ppr modname <+> text "->" <+>
                        (ppr m $$ pprAvails m as)
                    | (modname, (m, as)) <- Map.toList provs ]) $$
        hang (text "requires:") 10
              (vcat [ ppr modname <+> text "->" <+>
                        (hsep (punctuate comma (map ppr ms)) $$
                         pprAvails (mkModule holePackageKey modname) as)
                    | (modname, (ms, as)) <- Map.toList reqs])
      where provs = shapeProvides sh
            reqs = shapeRequires sh
            style m = let qual_name m' _ | m' == m = NameUnqual
                                         | otherwise = NameNotInScope2
                          qual = alwaysQualify {
                            queryQualifyName = qual_name
                            }
                      in mkDumpStyle qual
                      -- TODO: improve this to not qualify with a package key
                      -- if it's "local"
            pprAvails m as = withPprStyle (style m)
                                          (hsep (punctuate comma (map ppr as)))


-- | An empty shape suitable for initializing a shape context for shaping.
emptyShape :: Shape
emptyShape = Shape emptyModShape emptyAvailShape

emptyAvailShape :: AvailShape
emptyAvailShape = AvailShape Map.empty Map.empty

emptyModShape :: ModShape
emptyModShape = ModShape Map.empty Map.empty

shapeProvides :: Shape -> Map ModuleName (Module, [AvailInfo])
shapeProvides (Shape (ModShape mod _) (AvailShape avails _))
    = ASSERT2 (Map.keys mod == Map.keys avails, ppr mod $$ ppr avails)
      Map.intersectionWith (,) mod avails

shapeRequires :: Shape -> Map ModuleName ([Module], [AvailInfo])
shapeRequires (Shape (ModShape _ mods) (AvailShape _ avails))
    = ASSERT2 (Map.keys mods == Map.keys avails, ppr mods $$ ppr avails)
      Map.intersectionWith (,) mods avails
