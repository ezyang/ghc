module BackpackSyn(
    -- * Backpack abstract syntax
    LHsUnit, HsUnit(..),
    LHsUnitDecl, HsUnitDecl(..),
    HsDeclType(..),
    IncludeDecl(..),
    LInclSpec, InclSpec(..),
    LRenaming, Renaming(..),
    -- * Post shaping syntax
    LShPackage, ShPackage(..),
    LShUnitDecl, ShUnitDecl(..),
    ) where

import HsSyn
import RdrName
import SrcLoc
import Outputable
import Module
import PackageConfig
import HscTypes

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
                        Internal syntax
*                                                                      *
************************************************************************
-}

data ShPackage = ShPackage {
        shpkgName :: Located PackageName,
        shpkgBody :: [LShUnitDecl]
    }
type LShPackage = Located ShPackage

data ShUnitDecl
    = ShDecl ModSummary
    | ShInclude PackageKey
                (Map ModuleName Module)   -- provides (hs files)
                (Map ModuleName [Module]) -- requires (hsig files)
type LShUnitDecl = Located ShUnitDecl

instance Outputable ShUnitDecl where
    ppr (ShDecl summary) =
        (case ms_hsc_src summary of
            HsSrcFile -> text "module"
            HsigFile -> text "signature"
            HsBootFile -> text "module[boot]")
            <+> ppr (ms_mod summary)
    ppr (ShInclude pk provs reqs) =
        text "include" <+> ppr pk <+> ppr provs
            <+> text "requires" <+> ppr reqs
