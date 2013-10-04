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

// NB: keep this size something nice...
typedef struct rcthread_ {
    bdescr *nursery;
    void *workspaces; /* gen_workspace*, but that's not public */
} rcthread;

typedef struct ResourceContainer_ {
    char *label;
    struct ResourceContainer_ *link;
    struct ResourceContainer_ *parent;
    memcount max_blocks;
    memcount used_blocks;
    rcthread threads[FLEXIBLE_ARRAY];
} ResourceContainer;

extern ResourceContainer *RC_MAIN;
extern ResourceContainer *RC_LIST;

// reports failure if resource-container bound is hit
rtsBool allocGroupFor(bdescr **bd, W_ n, ResourceContainer *rc);
rtsBool allocBlockFor(bdescr **bd, ResourceContainer *rc);

// TODO: lock versions?

#endif /* RTS_RESOURCE_LIMITS_H */
