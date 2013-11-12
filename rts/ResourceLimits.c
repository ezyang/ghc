#include "Rts.h"
#include "RtsUtils.h"
#include "ResourceLimits.h"
#include "sm/GC.h"
#include "sm/Storage.h"
#include "Hash.h"
#include "sm/BlockAlloc.h"

#include <string.h>

ResourceContainer *RC_MAIN = NULL;
ResourceContainer *RC_LIST = NULL;

const char*
rc_status(ResourceContainer *rc)
{
    if (rc->status == RC_NORMAL) {
        return "NORMAL";
    } else {
        ASSERT(rc->status == RC_KILLED);
        return "KILLED";
    }
}

void
allocNotifyRC(ResourceContainer *rc, bdescr *bd)
{
    rc->used_blocks += bd->blocks;
    if (rc->max_blocks != 0 && rc->used_blocks > rc->max_blocks) {
        IF_DEBUG(gc, debugBelch("rc %s (%p) forced %d block allocation (to %ld/%ld)\n", rc->label, rc, bd->blocks, (long)rc->used_blocks, (long)rc->max_blocks));
        rc->status = RC_KILLED;
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
    ASSERT(rc->used_blocks >= bd->blocks);
    rc->used_blocks -= bd->blocks;
#ifdef DEBUG
    void *r =
        removeHashTable(rc->block_record, (StgWord)bd, NULL);
#endif
    // cast to the larger size
    ASSERT(r != NULL);
    ASSERT(r == (void*)bd->blocks);
    ASSERT(rc == bd->rc); // should be trivially true
    bd->rc = NULL;
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
                rc->status = RC_KILLED;
                IF_DEBUG(gc, debugBelch("rc %s (%p) out of memory (requested %ld at %ld/%ld)\n", rc->label, rc, (long)real, (long)rc->used_blocks, (long)rc->max_blocks));
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
    IF_DEBUG(sanity, memset(RC_MAIN->threads, 0xDD, n * sizeof(rcthread)));

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
    rc->parent = parent;
#ifdef DEBUG
    rc->block_record = allocHashTable();
#else
    rc->block_record = NULL;
#endif
    // initialize the workspaces
    IF_DEBUG(sanity, memset(rc->threads, 0xDD, n_capabilities * sizeof(rcthread)));
    initContainerGcThreads(rc, 0, n_capabilities);
    for (i = 0; i < n_capabilities; i++) {
        // ToDo: copied from allocNurseries
        rc->threads[i].nursery.blocks =
            allocNursery(NULL, RtsFlags.GcFlags.minAllocAreaSize, rc);
        rc->threads[i].nursery.n_blocks =
            RtsFlags.GcFlags.minAllocAreaSize;
        rc->threads[i].currentNursery = rc->threads[i].nursery.blocks;
    }
    // XXX add a lock here
    rc->link = RC_LIST;
    RC_LIST = rc;
    return rc;
}
