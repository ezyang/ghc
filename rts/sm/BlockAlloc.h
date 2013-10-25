/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-1999
 *
 * Block Allocator Interface
 *
 * ---------------------------------------------------------------------------*/

#ifndef BLOCK_ALLOC_H
#define BLOCK_ALLOC_H

#include "BeginPrivate.h"

bdescr *allocLargeChunk (W_ min, W_ max, ResourceContainer *rc);

/* Debugging  -------------------------------------------------------------- */

extern W_ countBlocks       (bdescr *bd);
extern W_ countAllocdBlocks (bdescr *bd);
extern W_ countBlocksWithoutRC       (bdescr *bd);
extern W_ countAllocdBlocksWithoutRC (bdescr *bd);
extern W_ inventoryBlocks       (bdescr *bd, ResourceContainer *rc);
extern W_ inventoryAllocdBlocks (bdescr *bd, ResourceContainer *rc);
extern void returnMemoryToOS(nat n);

W_ neededBlocks(W_ n);

#ifdef DEBUG
void checkFreeListSanity(void);
W_   countFreeList(void);
void markBlocks (bdescr *bd);
void reportUnmarkedBlocks (void);
#endif

extern W_ n_alloc_blocks;   // currently allocated blocks
extern W_ hw_alloc_blocks;  // high-water allocated blocks

#include "EndPrivate.h"

#endif /* BLOCK_ALLOC_H */
