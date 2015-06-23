module BackpackSyn(
    -- * Backpack abstract syntax
    LHsPackage, HsPackage(..),
    LHsPkgDecl, HsPkgDecl(..),
    HsDeclType(..),
    IncludeDecl(..),
    LInclSpec, InclSpec(..),
    LRenaming, Renaming(..),
    -- * Post shaping syntax
    LShPackage, ShPackage(..),
    LShPkgDecl, ShPkgDecl(..),
    ) where

import Shape
import HsSyn
import RdrName
import SrcLoc
import Outputable
import Module
import PackageConfig
import Avail
import HscTypes

import Data.Map (Map)
import qualified Data.Map as Map

{-
************************************************************************
*                                                                      *
                        User syntax
*                                                                      *
************************************************************************
-}

-- | Top level @package@ declaration in a Backpack file.
data HsPackage = HsPackage {
        hspkgName :: Located PackageName,
        hspkgExports :: Maybe LInclSpec,
        hspkgBody :: [LHsPkgDecl]
    }
type LHsPackage = Located HsPackage

-- | A declaration in a package, e.g. a module or signature definition,
-- or an include.
data HsDeclType = ModuleD | SignatureD
data HsPkgDecl
    = DeclD      HsDeclType (Located ModuleName) (Maybe (Located (HsModule RdrName)))
    | IncludeD   IncludeDecl
type LHsPkgDecl = Located HsPkgDecl

-- | An include of another package.
data IncludeDecl = IncludeDecl {
        idPackageName :: Located PackageName,
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
        shpkgBody :: [LShPkgDecl]
    }
type LShPackage = Located ShPackage

data ShPkgDecl
    = ShDecl ModSummary
    | ShInclude PackageKey ModShape
type LShPkgDecl = Located ShPkgDecl

instance Outputable ShPkgDecl where
    ppr (ShDecl ms) =
        (case ms_hsc_src ms of
            HsSrcFile -> text "module"
            HsigFile -> text "signature"
            HsBootFile -> text "module[boot]")
            <+> ppr (ms_mod ms)
    ppr (ShInclude pk (ModShape provs reqs)) =
        text "include" <+> ppr pk <+> ppr provs
            <+> text "requires" <+> ppr reqs
