/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team 1998-2008
 *
 * MegaBlock Allocator Interface.  This file contains all the dirty
 * architecture-dependent hackery required to get a chunk of aligned
 * memory from the operating system.
 *
 * ---------------------------------------------------------------------------*/

#include "PosixSource.h"
#include "Rts.h"

#include "RtsUtils.h"
#include "BlockAlloc.h"
#include "Trace.h"
#include "OSMem.h"

#include <string.h>

W_ peak_mblocks_allocated = 0;
W_ mblocks_allocated = 0;

/* -----------------------------------------------------------------------------
   Allocate new mblock(s)
   -------------------------------------------------------------------------- */

void *
getMBlock(void)
{
  return getMBlocks(1);
}

// The external interface: allocate 'n' mblocks, and return the
// address.

void *
getMBlocks(nat n)
{
    void *ret;

    ret = osGetMBlocks(n);

    debugTrace(DEBUG_gc, "allocated %d megablock(s) at %p",n,ret);
    
    mblocks_allocated += n;
    peak_mblocks_allocated = stg_max(peak_mblocks_allocated, mblocks_allocated);

    return ret;
}

void
freeMBlocks(void *addr, nat n)
{
    debugTrace(DEBUG_gc, "freeing %d megablock(s) at %p",n,addr);

    mblocks_allocated -= n;

    osFreeMBlocks(addr, n);
}

void
freeAllMBlocks(void)
{
    debugTrace(DEBUG_gc, "freeing all megablocks");

    osFreeAllMBlocks();
}

void
initMBlocks(void)
{
    osMemInit();
}
