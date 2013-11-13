#include "Rts.h"
#include "RtsUtils.h"
#include "ResourceLimits.h"
#include "sm/GC.h"
#include "sm/Storage.h"
#include "Hash.h"
#include "Schedule.h"
#include "sm/BlockAlloc.h"

#include <string.h>

ResourceContainer *RC_MAIN = NULL;
ResourceContainer *RC_LIST = NULL;

#ifdef DEBUG
static void sanityCheckListeners(ResourceContainer *rc)
{
    StgListener *p = rc->listeners;
    while (p->header.info == &stg_IND_info) {
        p = (StgListener*)((StgInd*)p)->indirectee;
    }
    if (rc->trigger_blocks != 0) {
        // Valid for trigger blocks to be less than the listener; we'll
        // trigger early and discover there is no work to do.
        ASSERT(p != END_LISTENER_LIST && p->limit >= rc->trigger_blocks);
    } else {
        ASSERT(p == END_LISTENER_LIST);
    }
    W_ limit = rc->trigger_blocks;
    while (p != END_LISTENER_LIST) {
        if (p->header.info == &stg_IND_info) {
            p = (StgListener*)((StgInd*)p)->indirectee;
            continue;
        }
        ASSERT(p->limit >= limit);
        limit = p->limit;
        p = p->link;
    }
    // check that they are lower than max_blocks? Don't have to...
}
#endif

const char*
rc_status(ResourceContainer *rc)
{
    if (rc->status == RC_NORMAL) {
        return "NORMAL";
    } else if (rc->status == RC_KILLED) {
        return "KILLED";
    } else {
        ASSERT(rc->status == RC_DEAD);
        return "DEAD";
    }
}

void
allocNotifyRC(ResourceContainer *rc, bdescr *bd)
{
    ASSERT(rc->status != RC_DEAD);
    rc->used_blocks += bd->blocks;
    if (rc->max_blocks != 0 && rc->used_blocks > rc->max_blocks) {
        IF_DEBUG(gc, debugBelch("rc %s (%p) forced %d block allocation (to %ld/%ld)\n", rc->label, rc, bd->blocks, (long)rc->used_blocks, (long)rc->max_blocks));
        killRC(rc);
    }
    bd->rc = rc;
    // we cannot distinguish zero blocks from NULL, fortunately zero
    // block bdescr is impossible
    ASSERT(bd->blocks != 0);
#ifdef DEBUG
    ASSERT(lookupHashTable(rc->block_record, (StgWord)bd) == NULL);
    insertHashTable(rc->block_record, (StgWord)bd, (void*)(StgWord)bd->blocks);
#endif
}

void
freeNotifyRC(ResourceContainer *rc, bdescr *bd)
{
    ASSERT(rc->status != RC_DEAD);
#ifdef DEBUG
    void *r =
        removeHashTable(rc->block_record, (StgWord)bd, NULL);
#endif
    // cast to the larger size
    ASSERT(r != NULL);
    ASSERT(rc->used_blocks >= bd->blocks);
    rc->used_blocks -= bd->blocks;
    ASSERT(r == (void*)bd->blocks);
    ASSERT(rc == bd->rc); // should be trivially true
    bd->rc = NULL;
}

/**
 * Perform a soft check to see if any listeners for an RC have
 * triggered. Try to do this as soon as possible after you do
 * an allocation, but some systems like GC will defer performing
 * this check until the end.  Yield as soon as possible if the
 * result of this is true.
 */
rtsBool
checkListenersRC(Capability *cap, ResourceContainer *rc)
{
    ASSERT(rc->status != RC_DEAD);
    rtsBool triggered = rtsFalse;
    // Only perform trigger_blocks check if hard limits are not
    // exceeded.  One consequence is that listeners for things
    // higher than max_blocks are not terribly useful.
    if (rc->used_blocks > rc->trigger_blocks) {
        // XXX locking
        // OK, walk listeners and wake up as many as we can trigger
        // (Might do no work!)
        StgListener *l = rc->listeners;
        while (l != END_LISTENER_LIST) {
            if (l->header.info == &stg_IND_info) {
                l = (StgListener*)((StgInd*)l)->indirectee;
                continue;
            }
            if (rc->used_blocks <= l->limit) break;
            // XXX should be failable
            // XXX who should the listener thread get charged to? The
            // *person who registered the listener*.  So this is not
            // right.
            IF_DEBUG(gc, debugBelch("rc %s (%p) triggered listener (limit=%ld at %ld/%ld)\n", rc->label, rc, (long)l->limit, (long)rc->used_blocks, (long)rc->max_blocks));
            StgTSO *t = createIOThread(cap, RtsFlags.GcFlags.initialStkSize, l->callback);
            pushOnRunQueue(cap, t); // bump to the front
            triggered = rtsTrue;
            StgListener *next = l->link;
            l->link = END_LISTENER_LIST;
            l = next;
        }
        rc->listeners = l;
        rc->trigger_blocks = l == END_LISTENER_LIST ? 0 : l->limit;
    }
    IF_DEBUG(sanity, sanityCheckListeners(rc));
    return triggered;
}

rtsBool
allocGroupFor(bdescr **pbd, W_ n, ResourceContainer *rc)
{
    // XXX calculate how many blocks this actually is going to be
    // (code duplication!)  We have to do this before we actually
    // commit to allocating any blocks
    W_ real = 0;
    // XXX synchronization
    if (rc->status == RC_NORMAL) {
        if (rc->max_blocks != 0) {
            real = neededBlocks(n);
            if (rc->used_blocks + real > rc->max_blocks) {
                // alternative: don't flip the status KILLED
                IF_DEBUG(gc, debugBelch("rc %s (%p) out of memory (requested %ld at %ld/%ld)\n", rc->label, rc, (long)real, (long)rc->used_blocks, (long)rc->max_blocks));
                killRC(rc);
                return rtsFalse;
            }
        }
    } else {
        ASSERT(rc->status == RC_KILLED);
        return rtsFalse;
    }
    bdescr *bd = allocGroup(n);
    ASSERT(real == 0 || bd->blocks == real);
    allocNotifyRC(rc, bd);
    *pbd = bd;
    return rtsTrue;
}

bdescr *
forceAllocGroupFor(W_ n, ResourceContainer *rc)
{
    bdescr *bd = allocGroup(n);
    allocNotifyRC(rc, bd);
    return bd;
}

rtsBool
allocBlockFor(bdescr **pbd, ResourceContainer *rc)
{
    return allocGroupFor(pbd, 1, rc);
}

bdescr *
forceAllocBlockFor(ResourceContainer *rc)
{
    return forceAllocGroupFor(1, rc);
}

void
initResourceLimits(void)
{
    nat n;
#if defined(THREADED_RTS)
#ifndef REG_Base
    n = 1;
#else
    n = RtsFlags.ParFlags.nNodes;
#endif /* REG_BASE */
#else
    n = 1;
#endif /* defined(THREADED_RTS) */
    // HACK! But we can't put this before initScheduler because the
    // scheduler needs to refer to RC_MAIN
    RC_MAIN = (ResourceContainer*)
        stgMallocBytes(sizeof(ResourceContainer) + n * sizeof(rcthread),
                       "initResourceLimits: RC_MAIN");
    RC_MAIN->label = "RC_MAIN";
    RC_MAIN->status = RC_NORMAL;
    RC_MAIN->link = NULL;
    RC_MAIN->parent = NULL;
    RC_MAIN->max_blocks = 0; // unlimited
    RC_MAIN->used_blocks = 0;
#ifdef DEBUG
    RC_MAIN->block_record = allocHashTable();
#else
    RC_MAIN->block_record = NULL;
#endif
    RC_MAIN->trigger_blocks = 0;
    RC_MAIN->pinned_object_block = NULL;
#ifdef THREADED_RTS
    // do not initialize RC_MAIN->lock; should not be used!
#endif
    IF_DEBUG(sanity, memset(RC_MAIN->threads, 0xDD, n * sizeof(rcthread)));
    // cannot initialize listeners yet because we don't have static
    // closures

    RC_LIST = RC_MAIN;
}

ResourceContainer *
newResourceContainer(nat max_blocks, ResourceContainer *parent)
{
    nat i;
    // XXX leaky; need to do something like unloadObj
    ResourceContainer *rc = stgMallocBytes(sizeof(ResourceContainer) + n_capabilities * sizeof(rcthread),
                                           "newResourceContainer");
    rc->status = RC_NORMAL;
    rc->label = "DYNAMIC(*)";
    rc->max_blocks = max_blocks;
    rc->used_blocks = 0; // will be bumped shortly
    rc->trigger_blocks = 0;
    rc->parent = parent;
#ifdef DEBUG
    rc->block_record = allocHashTable();
#else
    rc->block_record = NULL;
#endif
    rc->listeners = END_LISTENER_LIST;
    rc->pinned_object_block = NULL;
#ifdef THREADED_RTS
    initSpinLock(&rc->lock);
#endif
    // initialize the workspaces
    IF_DEBUG(sanity, memset(rc->threads, 0xDD, n_capabilities * sizeof(rcthread)));
    initContainerGcThreads(rc, 0, n_capabilities);
    for (i = 0; i < n_capabilities; i++) {
        // ToDo: copied from allocNurseries
        rc->threads[i].nursery.n_blocks =
            RtsFlags.GcFlags.minAllocAreaSize;
        rc->threads[i].nursery.blocks =
            allocNursery(NULL, &rc->threads[i].nursery.n_blocks, rc);
        rc->threads[i].currentNursery = rc->threads[i].nursery.blocks;
    }
    // XXX add a lock here
    rc->link = RC_LIST;
    RC_LIST = rc;
    return rc;
}

void
freeResourceContainer(ResourceContainer *rc)
{
    ASSERT(rc->status != RC_DEAD);
    nat i, g;
    bdescr *bd;
    rc->parent = NULL;
#ifdef DEBUG
    for (g = 0; g < RtsFlags.GcFlags.generations; g++) {
        generation *gen = &generations[g];
        for (bd = gen->blocks; bd != NULL; bd = bd->link) {
            ASSERT(bd->rc != rc);
        }
        for (bd = gen->old_blocks; bd != NULL; bd = bd->link) {
            ASSERT(bd->rc != rc);
        }
        for (bd = gen->large_objects; bd != NULL; bd = bd->link) {
            ASSERT(bd->rc != rc);
        }
    }
    ASSERT(rc->pinned_object_block == NULL);
#endif
    // TODO: maybe properly run all of them at the end
    rc->listeners = END_LISTENER_LIST;
    for (i = 0; i < n_capabilities; i++) {
        for (g = 0; g < RtsFlags.GcFlags.generations; g++) {
            gen_workspace *ws = &rc->threads[i].workspaces[g];
            freeWSDeque(ws->todo_q);
            ws->todo_q = NULL;
            freeChain(ws->part_list);
            freeChain(ws->scavd_list);
            freeChain(ws->todo_bd);
        }
        stgFree(rc->threads[i].workspaces);
        rc->threads[i].workspaces = NULL;
        freeChain(rc->threads[i].nursery.blocks);
    }
    ASSERT(rc->pinned_object_block == NULL);
    ASSERT(rc->used_blocks == 0);
#ifdef DEBUG
    ASSERT(keyCountHashTable(rc->block_record) == 0);
    freeHashTable(rc->block_record, NULL);
#endif
    IF_DEBUG(sanity, memset(rc->threads, 0xDD, n_capabilities * sizeof(rcthread)));
    rc->status = RC_DEAD;
}

// NB: We don't need to add any of these to the mutable list,
// as resource containers are considered roots, so everyone involved
// is guaranteed to get walked upon GC.
void listenRC(Capability *cap, ResourceContainer *rc, StgListener *listener)
{
    ASSERT(rc->status != RC_DEAD);
    ASSERT(listener->rc == rc);
    // XXX not synchronized
    W_ limit = listener->limit;
    StgListener *p = rc->listeners;
    StgListener **prev = &rc->listeners;
    while (p != END_LISTENER_LIST) {
        if (p->header.info == &stg_IND_info) {
            p = (StgListener*)((StgInd*)p)->indirectee;
            continue;
        }
        if (limit <= p->limit) {
            // insert it here
            *prev = listener;
            listener->link = p;
            break;
        }
        prev = &p->link;
        p = p->link;
    }
    if (p == END_LISTENER_LIST) {
        *prev = listener;
        listener->link = p;
    }
    if (prev == &rc->listeners) {
        rc->trigger_blocks = limit;
    }
    IF_DEBUG(sanity, sanityCheckListeners(rc));
    // immediately check if it fires
    checkListenersRC(cap, rc);
}

// XXX OK, actually, this can cause some really weird memory aliasing
// effects. So I really don't think this is the right way to go about
// implementing this.  Memory leak if you hold onto your Listener# too
// long after you free it.
void unlistenRC(StgListener *l) {
    // (checked by PrimOps.cmm)
    ASSERT(l->header.info == &stg_LISTENER_info);
    // XXX not synchronized
    StgListener *p = l->link;
    OVERWRITE_INFO(l, &stg_IND_info);
    ((StgInd*)l)->indirectee = (StgClosure*)p;
}

void markResourceContainers(evac_fn evac, void *user)
{
    ResourceContainer *rc;
    for (rc = RC_LIST; rc != NULL; rc = rc->link) {
        evac(user, (StgClosure **)&rc->listeners);
    }
}

void killRC(ResourceContainer *rc)
{
    if (rc->status == RC_DEAD) return;
    rc->status = RC_KILLED;
}
