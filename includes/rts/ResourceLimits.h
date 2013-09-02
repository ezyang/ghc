/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2013
 *
 * Macros and data structures for resource limits in STG code.
 *
 * Do not #include this file directly: #include "Rts.h" instead.
 *
 * To understand the structure of the RTS headers, see the wiki:
 *   http://hackage.haskell.org/trac/ghc/wiki/Commentary/SourceTree/Includes
 *
 */

#ifndef RTS_RESOURCE_LIMITS_H
#define RTS_RESOURCE_LIMITS_H

// ToDo: keeping this structure small might be important for performance
// if we can pack them together and that improves data locality
typedef struct ResourceContainer_ {
    StgInt rcID;

    char *label;

    // XXX: We actually need a nursery *per capability*, for now,
    // assume no_capabilities == 1
    bdescr *nursery;

    struct ResourceContainer_ *link;
} ResourceContainer;

extern ResourceContainer RC_MAIN[];

#endif /* RTS_RESOURCE_LIMITS_H */
