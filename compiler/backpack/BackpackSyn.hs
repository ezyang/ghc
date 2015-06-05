module BackpackSyn(
    -- * Backpack abstract syntax
    LHsPackage, HsPackage(..),
    LHsPkgDecl, HsPkgDecl(..),
    ModuleDecl,
    SignatureDecl,
    IncludeDecl(..),
    LInclSpec, InclSpec(..),
    LRenaming, Renaming(..),
    -- * Shape data types
    ShProvides, ShRequires,
    Shape(..), emptyShape,
    ) where

import HsSyn
import RdrName
import SrcLoc
import Outputable
import Module
import PackageConfig
import Avail

import Data.Map (Map)
import qualified Data.Map as Map

-- | Top level @package@ declaration in a Backpack file.
data HsPackage = HsPackage {
        hspkgName :: Located PackageName,
        hspkgExports :: Maybe LInclSpec,
        hspkgBody :: [LHsPkgDecl]
    }
type LHsPackage = Located HsPackage

-- | A declaration in a package, e.g. a module or signature definition,
-- or an include.
data HsPkgDecl
    = ModuleD    ModuleDecl
    | SignatureD SignatureDecl
    | IncludeD   IncludeDecl
type LHsPkgDecl = Located HsPkgDecl

type ModuleDecl = Located (HsModule RdrName)
type SignatureDecl  = Located (HsModule RdrName)

-- | An include of another package.
data IncludeDecl = IncludeDecl {
        idPackageName :: Located PackageName,
        idInclSpec :: Maybe LInclSpec
    }

-- | An include spec can rename/thin the provisions of a package
-- and rename the requirements of it.
data InclSpec = InclSpec {
        isProvides :: [ LRenaming ],
        isRequires :: [ LRenaming ]
    }
type LInclSpec = Located InclSpec
-- TODO: isProvides should be Maybe, remove maybe from idInclSpec.
-- Also need to support package identifiers here.

-- | Rename a module from one name to another.  The identity renaming
-- means that the module should be brought into scope.
data Renaming = Renaming { renameFrom :: ModuleName, renameTo :: ModuleName }
type LRenaming = Located Renaming

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

-- | Map from a module name to the set of signatures which specify
-- the provisions, and the (merged) specific names which are required.
-- Each 'Module' in @['Module']@ is of the form @p(A -> HOLE:A):A@
-- instead of @HOLE:A@: the reason we do this is that when we type check
-- a module which imports a requirement, we need to look up fixities,
-- instances, etc. which live in specific 'ModIface's of holes.
-- Tracking each signature file explicitly rather than merging them together
-- means we can give accurate dependency information.
type ShRequires = Map ModuleName ([Module], [AvailInfo])

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
                        (hsep (punctuate comma (map ppr ms)) $$
                         pprAvails (mkModule holePackageKey modname) as)
                    | (modname, (ms, as)) <- Map.toList reqs])
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
