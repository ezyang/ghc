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
        hsunitName :: Located ComponentName,
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
        idComponentName :: Located ComponentName,
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
        -- The INSTANTIATED package key for this include.
        -- So if we "include p requires (H)" and we happen to
        -- know that H is q:H, then is_uid is p(q:H).
        is_uid :: UnitId,
        -- is_provides and is_requires record the RENAMED but
        -- UN-INSTANTIATED names for modules.  So with
        -- "include p requires (H)", the recorded requirement
        -- is always H -> p(HOLE:H):H and not H -> p(q:H):H
        -- (even if we know it was instantiated that way.)
        -- The point is that this lets us know how to read
        -- in interfaces, and then we can instantiate with
        -- the actual implementation ourselves.
        is_provides :: Map ModuleName Module,
        is_requires :: Map ModuleName Module,
        -- When actually compiling, we want the real RENAMED
        -- and INSTANTIATED provides/requires.  So they're saved here.
        is_inst_provides :: Map ModuleName Module,
        is_inst_requires :: Map ModuleName Module
    }

-- Note [is_provides versus is_inst_provides]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Suppose we are compiling the unit:
--
--      include m-impl (M)
--      include p requires (H as M)
--
-- Through pre-shaping, we know that we will need modules from
-- p(H -> m-impl:M).  However, prior to shaping, we do not actually
-- know that this substitution is VALID: if m-impl:M doesn't implement
-- all the requirements of p, we need to give an error.  Furthermore,
-- unification may occur when we do this (say M reexports something from
-- signature A), so the process of checking that the substitution is
-- valid has side-effects.
--
-- We do have one codepath which can check this: computeInterface (rnInterface),
-- which is ordinary used to implement lazy interface loading during type
-- checking.  But: (1) rnInterface does too much work; we just want to look at
-- mi_exports and not the entire interface, and (2) if something is missing,
-- computeInterface has no good way of reporting an error.  So, for
-- computeInterface on a module assumes that the instantiation is *good*,
-- and we need a different strategy.
--
-- A different strategy is cunningly use computeInterface ONLY to handle
-- renaming due to requirements, and then merge the names ourselves after
-- the fact.  Thus, is_provides and is_requires have the UNINSTANTIATED
-- (according to the source unit) modules which ARE renamed according to
-- the specification.  We can load these interfaces, which is guaranteed
-- to work, and then check for everything being good.  Once this check
-- is complete, we are allowed to actually load the interfaces referred
-- to by is_inst_provides, which we otherwise would not have known about.

instance Outputable IncludeSummary where
    ppr IncludeSummary{ is_uid = pk, is_provides = provs, is_requires = reqs }
        = text "include" <+> ppr pk <+> ppr provs <+> text "requires" <+> ppr reqs

type IncludeGraph = [IncludeSummary]
