#include "Rts.h"
#include "RtsUtils.h"
#include "ResourceLimits.h"
#include "sm/GC.h"
#include "sm/Storage.h"
#include "sm/BlockAlloc.h"

ResourceContainer *RC_MAIN = NULL;
ResourceContainer *RC_LIST = NULL;

const char*
rc_status(ResourceContainer *rc)
{
    if (rc->status == RC_NORMAL) {
        return "NORMAL";
    } else if (rc->status == RC_RECOVERING) {
        return "RECOVERING";
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
    // Idea: normally, check against soft limit. However, if the
    // container is recovering from an exception thrown from exceeding
    // the soft limit, check for the hard limit instead.  Note that
    // the user needs to explicitly set a thread back to normal state
    // in order to trigger soft exceptions to be thrown again.
    //
    // NB: soft_max_blocks <= hard_max_blocks
    if (rc->status == RC_NORMAL) {
        if (rc->soft_max_blocks != 0) {
            real = neededBlocks(n);
            if (rc->used_blocks + real > rc->soft_max_blocks) {
                rc->status = RC_RECOVERING;
                return rtsFalse;
            }
        }
    } else if (rc->status == RC_RECOVERING) {
        if (rc->hard_max_blocks != 0) {
            real = neededBlocks(n);
            if (rc->used_blocks + real > rc->hard_max_blocks) {
                rc->status = RC_KILLED;
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
    ASSERT(rc->used_blocks > rc->hard_max_blocks);
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
    RC_MAIN->soft_max_blocks = 0; // unlimited
    RC_MAIN->hard_max_blocks = 0; // unlimited
    RC_MAIN->used_blocks = 0; // XXX inaccurate but whatever
    IF_DEBUG(sanity, memset(RC_MAIN->threads, 0xDD, n * sizeof(rcthread)));

    RC_LIST = RC_MAIN;
}

ResourceContainer *
newResourceContainer(nat max_blocks, ResourceContainer *parent)
{
    // XXX leaky; need to do something like unloadObj
    ResourceContainer *rc = stgMallocBytes(sizeof(ResourceContainer), "newResourceContainer");
    rc->label = "DYNAMIC(*)";
    rc->soft_max_blocks = max_blocks;
    rc->hard_max_blocks = max_blocks + 8; // XXX make customizable
    rc->used_blocks = 0; // will be bumped shortly
    rc->parent = parent;
    // initialize the workspaces
    initContainerGcThreads(rc, 0, n_capabilities);
    // XXX add a lock here
    rc->link = RC_LIST;
    RC_LIST = rc;
    return rc;
}
