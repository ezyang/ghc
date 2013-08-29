/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2008
 *
 * MegaBlock Allocator interface.
 *
 * See wiki commentary at
 *  http://hackage.haskell.org/trac/ghc/wiki/Commentary/HeapAlloced
 *
 * ---------------------------------------------------------------------------*/

#ifndef RTS_STORAGE_MBLOCK_H
#define RTS_STORAGE_MBLOCK_H

extern W_ peak_mblocks_allocated;
extern W_ mblocks_allocated;

extern void initMBlocks(void);
extern void * getMBlock(void);
extern void * getMBlocks(nat n);
extern void freeMBlocks(void *addr, nat n);
extern void freeAllMBlocks(void);

/* -----------------------------------------------------------------------------
   The HEAP_ALLOCED() test.

   HEAP_ALLOCED is called FOR EVERY SINGLE CLOSURE during GC.
   It needs to be FAST.

   See wiki commentary at
     http://hackage.haskell.org/trac/ghc/wiki/Commentary/HeapAlloced
   -------------------------------------------------------------------------- */

#define HEAP_ALLOCED(p) ((Bdescr(p)->flags & BF_STATIC) == 0)
#define HEAP_ALLOCED_GC HEAP_ALLOCED

#endif /* RTS_STORAGE_MBLOCK_H */
