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
    memcount n_words;
    // NB: needs lock. Do it properly: do it PER thread
    // block for allocating pinned objects into
    bdescr *pinned_object_block;
#ifdef THREADED_RTS
#if defined(PROF_SPIN)
    SpinLock lock;
#else
    SpinLock lock;
    StgWord lock_padding;
#endif
#else
    StgWord lock_padding[2];
#endif
    StgWord padding[4]; // make it a nice multiple, don't know if this actually helps
    rcthread threads[FLEXIBLE_ARRAY];
} ResourceContainer;

#define RC_NORMAL       0
#define RC_RECOVERING   1
#define RC_KILLED       2
#define RC_DEAD         3

rtsBool allocGroupFor(bdescr **pbd, W_ n, ResourceContainer *rc);
rtsBool allocBlockFor(bdescr **pbd, ResourceContainer *rc);

bdescr *forceAllocGroupFor(W_ n, ResourceContainer *rc);
bdescr *forceAllocBlockFor(ResourceContainer *rc);

void initResourceLimits(void);
ResourceContainer *newResourceContainer(nat max_blocks, ResourceContainer *parent);
void freeResourceContainer(ResourceContainer *rc);
rtsBool isDeadResourceContainer(ResourceContainer *rc);

void killRC(ResourceContainer *rc);

const char *rc_status(ResourceContainer *rc);

#include "EndPrivate.h"

#endif /* RESOURCE_LIMITS_H */
