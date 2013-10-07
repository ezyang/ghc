#include "Rts.h"
#include "RtsUtils.h"
#include "ResourceLimits.h"
#include "sm/GC.h"

ResourceContainer *RC_MAIN = NULL;
ResourceContainer *RC_LIST = NULL;

rtsBool
allocGroupFor(bdescr **pbd, W_ n, ResourceContainer *rc)
{
    // XXX calculate how many blocks this actually is going to be
    // (code duplication!)  We have to do this before we actually
    // commit to allocating any blocks
    W_ real = 0;
    if (rc->max_blocks != 0) {
        if (n >= BLOCKS_PER_MBLOCK) {
            real = BLOCKS_TO_MBLOCKS(n) * BLOCKS_PER_MBLOCK;
        } else {
            real = n;
        }
        // check and make sure that we're within our limits
        if (rc->used_blocks + real > rc->max_blocks) {
            return rtsFalse;
        }
    }
    bdescr *bd = allocGroup(n);
    ASSERT(real == 0 || bd->blocks == real);
    bd->rc = rc;
    *pbd = bd;
    return rtsTrue;
}

rtsBool
allocBlockFor(bdescr **pbd, ResourceContainer *rc)
{
    return allocGroupFor(pbd, 1, rc);
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
    rc->max_blocks = max_blocks;
    rc->used_blocks = 0; // will be bumped shortly
    rc->parent = parent;
    // initialize the workspaces
    initContainerGcThreads(rc, 0, n_capabilities);
    // XXX add a lock here
    rc->link = RC_LIST;
    RC_LIST = rc;
    return rc;
}
