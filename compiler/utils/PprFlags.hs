module PprFlags (PprFlags(..)) where

import Platform

data PprFlags = PprFlags {
  pprUserLength         :: Int,
  pprCols               :: Int,

  useUnicode      :: Bool,
  useUnicodeSyntax :: Bool,
  targetPlatform :: Platform,

  suppressUniques :: Bool,
  errorSpans :: Bool,
  suppressModulePrefixes :: Bool,
  printExplicitKinds :: Bool,
  printExplicitForalls :: Bool,
  suppressTypeSignatures :: Bool,
  suppressIdInfo :: Bool,
  suppressCoercions :: Bool,
  pprCaseAsLet :: Bool,
  pprShowTicks :: Bool,
  suppressTypeApplications :: Bool,
  sccProfilingOn :: Bool,

  dummy :: ()
    }
