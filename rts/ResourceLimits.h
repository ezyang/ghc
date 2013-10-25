#ifndef RESOURCE_LIMITS_H
#define RESOURCE_LIMITS_H

#include "sm/GCThread.h"
#include "Hash.h"

#include "BeginPrivate.h"

// NB: keep this size something nice...
typedef struct rcthread_ {
    bdescr *currentNursery;
    nursery nursery;
    gen_workspace *workspaces;
} rcthread;

typedef struct ResourceContainer_ {
    char *label;
    struct ResourceContainer_ *link;
    struct ResourceContainer_ *parent;
    memcount max_blocks;
    // XXX no soft limits for now
    union {
        memcount count; // used when sanity-checking resource container block counts
    } u;
    memcount used_blocks;
    StgWord status;
    HashTable *block_record;
    StgWord padding[8]; // make it a nice multiple, don't know if this actually helps
    rcthread threads[FLEXIBLE_ARRAY];
} ResourceContainer;

#define RC_NORMAL       0
#define RC_RECOVERING   1
#define RC_KILLED       2

rtsBool allocGroupFor(bdescr **pbd, W_ n, ResourceContainer *rc);
rtsBool allocBlockFor(bdescr **pbd, ResourceContainer *rc);

bdescr *forceAllocGroupFor(W_ n, ResourceContainer *rc);
bdescr *forceAllocBlockFor(ResourceContainer *rc);

void initResourceLimits(void);
ResourceContainer *newResourceContainer(nat max_blocks, ResourceContainer *parent);

const char *rc_status(ResourceContainer *rc);

#include "EndPrivate.h"

#endif /* RESOURCE_LIMITS_H */
