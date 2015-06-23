module BackpackSyn(
    -- * Backpack abstract syntax
    LHsUnit, HsUnit(..),
    LHsUnitDecl, HsUnitDecl(..),
    HsDeclType(..),
    IncludeDecl(..),
    LInclSpec, InclSpec(..),
    LRenaming, Renaming(..),
    -- * IR bits
    IncludeSummary(..), IncludeGraph,
    ) where

import HsSyn
import RdrName
import SrcLoc
import Outputable
import Module
import PackageConfig
import UniqSet

import Data.Map (Map)

{-
************************************************************************
*                                                                      *
                        User syntax
*                                                                      *
************************************************************************
-}

-- | Top level @package@ declaration in a Backpack file.
data HsUnit = HsUnit {
        hsunitName :: Located UnitName,
        hsunitExports :: Maybe LInclSpec,
        hsunitBody :: [LHsUnitDecl]
    }
type LHsUnit = Located HsUnit

-- | A declaration in a package, e.g. a module or signature definition,
-- or an include.
data HsDeclType = ModuleD | SignatureD
data HsUnitDecl
    = DeclD      HsDeclType (Located ModuleName) (Maybe (Located (HsModule RdrName)))
    | IncludeD   IncludeDecl
type LHsUnitDecl = Located HsUnitDecl

-- | An include of another package.
data IncludeDecl = IncludeDecl {
        idUnitName :: Located UnitName,
        idInclSpec :: Maybe LInclSpec
    }

-- | An include spec can rename/thin the provisions of a package
-- and rename the requirements of it.
data InclSpec = InclSpec {
        isProvides :: Maybe [ LRenaming ],
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
                        IR
*                                                                      *
************************************************************************
-}

-- | An include declaration which can be topologically sorted.
data IncludeSummary = IncludeSummary {
        is_ldecl :: Located IncludeDecl,
        is_pkg_key :: UnitKey,
        is_provides :: Map ModuleName Module,
        is_requires :: UniqSet ModuleName
    }
instance Outputable IncludeSummary where
    ppr IncludeSummary{ is_pkg_key = pk, is_provides = provs, is_requires = reqs }
        = text "include" <+> ppr pk <+> ppr provs <+> text "requires" <+> ppr reqs

type IncludeGraph = [IncludeSummary]

