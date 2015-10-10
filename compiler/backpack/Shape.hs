module Shape(
    -- * Shape data types
    ShProvides, ShRequires,
    Shape(..), emptyShape,
    ) where

import Outputable
import Module
import Avail

import Data.Map (Map)
import qualified Data.Map as Map

{-
************************************************************************
*                                                                      *
                        Shapes
*                                                                      *
************************************************************************
-}

-- | Map from a module name to the 'Module' identity which provides it,
-- and what it exports.
type ShProvides = Map ModuleName (Module, [AvailInfo])

-- | Map from a module name to the specific names which are required.
-- We don't track the 'Module' identity, because it is always 'hole:A'.
type ShRequires = Map ModuleName [AvailInfo]

-- | The shape of a package is what modules it provides, and what modules
-- it requires.
data Shape = Shape {
        sh_provides :: ShProvides,
        sh_requires :: ShRequires
    }

instance Outputable Shape where
    ppr (Shape provs reqs) =
        hang (text "provides:") 10
              (vcat [ ppr modname <+> text "->" <+>
                        (ppr m $$ pprAvails m as)
                    | (modname, (m, as)) <- Map.toList provs ]) $$
        hang (text "requires:") 10
              (vcat [ ppr modname <+> text "->" <+>
                         pprAvails (mkModule holeUnitId modname) as
                    | (modname, as) <- Map.toList reqs])
      where style m = let qual_name m' _ | m' == m = NameUnqual
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
emptyShape = Shape { sh_provides = Map.empty, sh_requires = Map.empty }
