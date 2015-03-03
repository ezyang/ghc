--                                                              -*-haskell-*-
{
{-# LANGUAGE BangPatterns #-} -- required for versions of Happy before 1.18.6
module BackpackParser (parsePackages) where

-- compiler/main
import Backpack
import PackageConfig

-- compiler/utils
import OrdList
import FastString

-- compiler/basicTypes
import SrcLoc
import Module

-- compiler/parser
import Lexer

}

%token
 'where'        { L _ ITwhere }
 'as'           { L _ ITas }
 ';'            { L _ ITsemi }
 ':'            { L _ ITcolon }
 ','            { L _ ITcomma }
 '('            { L _ IToparen }
 ')'            { L _ ITcparen }
 '{'            { L _ ITocurly }                        -- special symbols
 '}'            { L _ ITccurly }
 -- The fact that IDs overlap with CONIDs is pretty ugly, but unavoidable
 -- since some valid package names coincide with valid module names.
 -- NB: You should never get a CONID token, ID should always
 -- override.  But just in case...
 ID             { L _ (ITvarid _) }
 CONID          { L _ (ITconid _) }
 QCONID         { L _ (ITqconid _) }
 vocurly        { L _ ITvocurly } -- virtual open curly (from layout)
 vccurly        { L _ ITvccurly } -- virtual close curly (from layout)
 'includes'             { L _ ITincludes }
 'exposed-modules'      { L _ ITexposed_modules }
 'other-modules'        { L _ ITother_modules }
 'exposed-signatures'   { L _ ITexposed_signatures }
 'required-signatures'  { L _ ITrequired_signatures }
 'reexported-modules'   { L _ ITreexported_modules }
 'source-dir'           { L _ ITsource_dir }
 'package'              { L _ ITpackage }
 'executable'           { L _ ITexecutable }
 'main-is'              { L _ ITmain_is }
 'installed-id'         { L _ ITinstalled_id }
 'installed'            { L _ ITinstalled }
 -- Order matters!
 STRING          { L _ (ITstring _ _) }

%monad { P } { >>= } { return }
%lexer { (lexer True) } { L _ ITeof }
%tokentype { (Located Token) }

%name parsePackages backpack

%%


backpack :: { [Located Backpack] }
    : implicit_top packages close { $2 }
    | '{' packages '}' { $2 }

implicit_top :: { () }
    : {- empty -} {% pushCurrentContext }

-- TODO: switch to left recursion (maybe?)
packages :: { [Located Backpack] }
    : package ';' packages  { $1 : $3 }
    -- YES THIS RULE IS IMPORTANT (and it's packages if you OrdList it)
    | package ';' { [$1] }
    | package               { [$1] }

-- TODO: record which keyword was used and complain if you use the wrong one
package :: { Located Backpack }
    : 'package' pkgname 'where' vocurly fields close { sLL $1 (last $5) (foldr ($) (emptyBackpack (unLoc $2)) (map unLoc $5)) }
    | 'package' pkgname 'where' '{' fields '}' { sLL $1 $> (foldr ($) (emptyBackpack (unLoc $2)) (map unLoc $5)) }
    | 'executable' path 'where' vocurly fields close { sLL $1 (last $5) (foldr ($) emptyExecutable { backpackOutputFile = Just $2, backpackExecutable = Just $2 } (map unLoc $5)) }
    -- | 'executable' path 'includes' includes { sLL $1 (last $4) () }

fields :: { [Located BackpackField] }
    : field ';' fields { $1 : $3 }
    | field ';' { [$1] }
    | field { [$1] }

field :: { Located BackpackField }
    : 'includes' ':' includes { sLL $1 (last $>) (\b -> b { backpackIncludes = $3 }) }
    | 'exposed-modules' ':' modids { sLL $1 (last $>) (\b -> b { backpackExposedModules = $3 }) }
    | 'other-modules' ':' modids { sLL $1 (last $>) (\b -> b { backpackOtherModules = $3 }) }
    | 'exposed-signatures' ':' modids { sLL $1 (last $>) (\b -> b { backpackExposedSignatures = $3}) }
    | 'required-signatures' ':' modids { sLL $1 (last $>) (\b -> b { backpackRequiredSignatures = $3 }) }
    | 'source-dir' ':' path { sLL $1 $3 (\b -> b { backpackSourceDir = Just $3}) }
    | 'reexported-modules' ':' renames { sLL $1 (last $>) (\b -> b { backpackReexportedModules = $3 } ) }
    | 'main-is' ':' path { sLL $1 $3 (\b -> b { backpackExecutable = Just $3}) }

modids :: { [Located ModuleName] }
    : modid { [$1] }
    | modid modids { $1 : $2 }

includes :: { [Located PkgInclude]  }
    : include ',' includes { $1 : $3 }
    | include ',' { [$1] }
    | include { [$1] }

include :: { Located PkgInclude }
    : pkgname { sL1 $1 (PkgInclude (unLoc $1) Nothing) }
    | pkgname '(' renames ')' { sLL $1 $> (PkgInclude (unLoc $1) (Just $3)) }

renames :: { [Located (ModuleName, ModuleName)] }
    : rename ',' renames { $1 : $3 }
    | rename ',' { [$1] }
    | rename { [$1] }

rename :: { Located (ModuleName, ModuleName) }
    : modid 'as' modid  { sLL $1 $> (unLoc $1, unLoc $3) }
    | modid { sL1 $1 (unLoc $1, unLoc $1) }

pkgname :: { Located PackageName }
    : STRING     { sL1 $1 $ PackageName (getSTRING $1) }
    | special_id { sL1 $1 $ PackageName (unLoc $1) }
    | ID         { sL1 $1 $ PackageName (getID $1) }

path :: { Located FilePath }
    : STRING { sL1 $1 . unpackFS $ getSTRING $1 }
    | special_id { sL1 $1 $ unpackFS (unLoc $1) }
    | ID         { sL1 $1 $ unpackFS (getID $1) }

modid   :: { Located ModuleName }
        : ID                    { sL1 $1 $ mkModuleNameFS (getID $1) }
        | CONID                 { sL1 $1 $ mkModuleNameFS (getCONID $1) }
        | QCONID                { sL1 $1 $ let (mod,c) = getQCONID $1 in
                                  mkModuleNameFS
                                   (mkFastString
                                     (unpackFS mod ++ '.':unpackFS c))
                                }

special_id :: { Located FastString }
special_id
        : 'includes'                { sL1 $1 (fsLit "includes") }
        | 'exposed-modules'         { sL1 $1 (fsLit "exposed-modules") }
        | 'other-modules'           { sL1 $1 (fsLit "other-modules") }
        | 'exposed-signatures'      { sL1 $1 (fsLit "exposed-signatures") }
        | 'required-signatures'     { sL1 $1 (fsLit "required-signatures") }
        | 'reexported-modules'      { sL1 $1 (fsLit "reexported-modules") }
        | 'source-dir'              { sL1 $1 (fsLit "source-dir") }
        | 'package'                 { sL1 $1 (fsLit "package") }
        | 'executable'              { sL1 $1 (fsLit "executable") }
        | 'main-is'                 { sL1 $1 (fsLit "main-is") }
        | 'installed'               { sL1 $1 (fsLit "installed") }
        | 'installed-id'            { sL1 $1 (fsLit "installed-id") }

-- Stolen from Parser.y

close :: { () }
        : vccurly               { () } -- context popped in lexer.
        | error                 {% popContext }

{
-- TODO These are copied from Parser.y; refactor this into a ParserUtils
-- module at some point.

happyError :: P a
happyError = srcParseFail

-- Make a source location for the file.  We're a bit lazy here and just
-- make a point SrcSpan at line 1, column 0.  Strictly speaking we should
-- try to find the span of the whole file (ToDo).
fileSrcSpan :: P SrcSpan
fileSrcSpan = do
  l <- getSrcLoc;
  let loc = mkSrcLoc (srcLocFile l) 1 1;
  return (mkSrcSpan loc loc)

getSTRING       (L _ (ITstring _ x)) = x
getID           (L _ (ITvarid    x)) = x
getCONID        (L _ (ITconid    x)) = x
getQCONID       (L _ (ITqconid   x)) = x

-- Utilities for combining source spans
comb2 :: Located a -> Located b -> SrcSpan
comb2 a b = a `seq` b `seq` combineLocs a b

comb3 :: Located a -> Located b -> Located c -> SrcSpan
comb3 a b c = a `seq` b `seq` c `seq`
    combineSrcSpans (getLoc a) (combineSrcSpans (getLoc b) (getLoc c))

comb4 :: Located a -> Located b -> Located c -> Located d -> SrcSpan
comb4 a b c d = a `seq` b `seq` c `seq` d `seq`
    (combineSrcSpans (getLoc a) $ combineSrcSpans (getLoc b) $
                combineSrcSpans (getLoc c) (getLoc d))

-- strict constructor version:
{-# INLINE sL #-}
sL :: SrcSpan -> a -> Located a
sL span a = span `seq` a `seq` L span a

-- replaced last 3 CPP macros in this file
{-# INLINE sL0 #-}
sL0 = L noSrcSpan       -- #define L0   L noSrcSpan

{-# INLINE sL1 #-}
sL1 x = sL (getLoc x)   -- #define sL1   sL (getLoc $1)

{-# INLINE sLL #-}
sLL x y = sL (comb2 x y) -- #define LL   sL (comb2 $1 $>)
}
