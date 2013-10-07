#include "Rts.h"
#include "RtsUtils.h"
#include "ResourceLimits.h"
#include "sm/GC.h"
#include "sm/Storage.h"
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
    bd->rc = rc;
    rc->used_blocks += bd->blocks;
    *pbd = bd;
    return rtsTrue;
}

bdescr *
forceAllocGroupFor(W_ n, ResourceContainer *rc)
{
    bdescr *bd = allocGroup(n);
    rc->used_blocks += bd->blocks;
    // Note: the following assertion is not true: in allocate() (to be
    // renamed forceAllocate) we unconditionally do a forced allocation,
    // to avoid inducing a phase shift when we cannot actually promise
    // that an exception will get delivered.
    // ASSERT(rc->used_blocks > rc->max_blocks);
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
    RC_MAIN->link = NULL;
    RC_MAIN->parent = NULL;
    RC_MAIN->max_blocks = 0; // unlimited
    RC_MAIN->used_blocks = 0;
    IF_DEBUG(sanity, memset(RC_MAIN->threads, 0xDD, n * sizeof(rcthread)));

    RC_LIST = RC_MAIN;
}

