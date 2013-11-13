#ifndef RESOURCE_LIMITS_H
#define RESOURCE_LIMITS_H

#include "sm/GCThread.h"
#include "sm/GC.h"
#include "Hash.h"

#include "BeginPrivate.h"

// NB: keep this size something nice...
typedef struct rcthread_ {
    bdescr *currentNursery;
    nursery nursery;
    gen_workspace *workspaces;
} rcthread;

// NB: There is a kind of delicate invariant being maintained here,
// which is that the offset of 'threads' is something compiler needs
// to know about, since it is baked into all of the Haskell code you
// compile (for saving and loading thread state).  So this structure
// cannot be conditionalized on RTS-only conditions, e.g. DEBUG or
// THREADED
typedef struct ResourceContainer_ {
    char *label;
    struct ResourceContainer_ *link;
    struct ResourceContainer_ *parent;
    // ToDo add synchronization for THREADED
    StgListener *listeners;
    // NB: this is may be an underestimate, if a relevant listener
    // was unregistered
    memcount trigger_blocks;
    memcount max_blocks;
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
    StgWord padding[2]; // make it a nice multiple, don't know if this actually helps
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

void allocNotifyRC(ResourceContainer *rc, bdescr *bd);
void freeNotifyRC(ResourceContainer *rc, bdescr *bd);

void initResourceLimits(void);
ResourceContainer *newResourceContainer(nat max_blocks, ResourceContainer *parent);
void freeResourceContainer(ResourceContainer *rc);

rtsBool checkListenersRC(Capability *cap, ResourceContainer *rc);
void listenRC(Capability *cap, ResourceContainer *rc, StgListener *listener);
void unlistenRC(StgListener *listener);
void killRC(ResourceContainer *rc);
#define END_LISTENER_LIST  ((StgListener*)STATIC_CLOSURE(stg_END_LISTENER_LIST))

const char *rc_status(ResourceContainer *rc);

void markResourceContainers(evac_fn evac, void *user);

#include "EndPrivate.h"

#endif /* RESOURCE_LIMITS_H */
