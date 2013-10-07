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

typedef struct ResourceContainer_ ResourceContainer;

extern ResourceContainer *RC_MAIN;
extern ResourceContainer *RC_LIST;

// reports failure if resource-container bound is hit
rtsBool allocGroupFor(bdescr **bd, W_ n, ResourceContainer *rc);
rtsBool allocBlockFor(bdescr **bd, ResourceContainer *rc);

// TODO: lock versions?

#endif /* RTS_RESOURCE_LIMITS_H */
