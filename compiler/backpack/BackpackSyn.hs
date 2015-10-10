module BackpackSyn(
    -- * Backpack abstract syntax
    HsComponentId(..),
    LHsUnit, HsUnit(..),
    LHsUnitDecl, HsUnitDecl(..),
    HsDeclType(..),
    IncludeDecl(..),
    LInclSpec, InclSpec(..),
    LRenaming, Renaming(..),
    ) where

import HsSyn
import RdrName
import SrcLoc
import Outputable
import Module
import PackageConfig

{-
************************************************************************
*                                                                      *
                        User syntax
*                                                                      *
************************************************************************
-}

data HsComponentId = HsComponentId {
    hsPackageName :: PackageName,
    hsComponentId :: ComponentId
    }

instance Outputable HsComponentId where
    ppr (HsComponentId _pn cid) = ppr cid -- todo debug with pn

-- | Top level @package@ declaration in a Backpack file.
data HsUnit n = HsUnit {
        hsunitName :: Located n,
        hsunitExports :: Maybe LInclSpec,
        hsunitBody :: [LHsUnitDecl n]
    }
type LHsUnit n = Located (HsUnit n)

-- | A declaration in a package, e.g. a module or signature definition,
-- or an include.
data HsDeclType = ModuleD | SignatureD
data HsUnitDecl n
    = DeclD      HsDeclType (Located ModuleName) (Maybe (Located (HsModule RdrName)))
    | IncludeD   (IncludeDecl n)
type LHsUnitDecl n = Located (HsUnitDecl n)

-- | An include of another package.
data IncludeDecl n = IncludeDecl {
        idInclude :: Located n,
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
