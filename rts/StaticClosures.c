/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2013
 *
 * Responsible for copying static closures into proper blocks so that
 * bdescr works.
 *
 * ---------------------------------------------------------------------------*/

#include "Rts.h"
#include "StaticClosures.h"

#include <string.h>

StaticClosureInds *SCI_LIST = NULL;

// these are not publically exported

extern StgIntCharlikeClosure stg_CHARLIKE_static_closure[];
extern StgIntCharlikeClosure stg_INTLIKE_static_closure[];

// very similar to the scavenge code

#ifdef THREADED_RTS
Mutex static_closures_mutex;
#endif

static void initialize_field(StgClosure **p);
static void ensureFreeSpace(int);
static W_ static_blocks = 0;
static bdescr *current_block = NULL;

W_ countStaticBlocks() {
    return static_blocks;
}

void
initialize_field(StgClosure **p)
{
    // The field of a static closure starts off as an *untagged* pointer
    // to the *indirection*.  So we short-circuit through the
    // indirection... and pick up the appropriate tag from the
    // destination of the indirection.
    StgClosure *q = *p;
    ASSERT(GET_CLOSURE_TAG(q) == 0);
    StgClosure *r = *(StgClosure**)q;
    ASSERT(LOOKS_LIKE_CLOSURE_PTR(r));
    *p = r;
}

// Helper debug function for when you're in GDB.
// Calculate the arguments by running 'objdump -h executable'
// and look for the 'staticclosureinds' section:
//
//Idx Name              SIZE      VMA               LMA               File off  Algn
// 25 staticclosureinds 00003090  0000000000742748  0000000000742748  00142748  2**3
//
// Then run checkStaticClosures(VMA, VMA+SIZE) after initStaticClosures
// to check if initialization was good.  The way we test for this is
// looking for any pointers which are still pointing into the
// indirections (this is how it is initialized).
void
checkStaticClosures(StgClosure **section_start, StgClosure **section_end) {
    StgClosure **pp;
    for (pp = section_start; pp < section_end; pp++) {
        StgClosure *p = UNTAG_CLOSURE(*pp);
        // Not perfect, but will segfault if it's not actually a block
        ASSERT(!HEAP_ALLOCED(p));
        // TODO: sanity check tagging
        const StgInfoTable *info = get_itbl(p);
        switch (info->type) {
        case FUN_STATIC:
        case THUNK_STATIC:
        case CONSTR_STATIC:
        case CONSTR_NOCAF_STATIC:
          {
            StgClosure **q, **end;

            end = ((StgClosure**)p->payload) + info->layout.payload.ptrs;
            for (q = p->payload; q < end; q++) {
                ASSERT(!(*q >= (StgClosure*)section_start &&
                         *q <  (StgClosure*)section_end));
            }
            break;
          }
        case IND_STATIC:
            ASSERT(!(((StgInd*)p)->indirectee >= (StgClosure*)section_start &&
                     ((StgInd*)p)->indirectee <  (StgClosure*)section_end));
            break;
        default:
            barf("checkStaticClosures: strange closure type %d",
                 (int)(info->type));
        }
    }
}

// Ensure there are size_w words available in the current block; allocating
// a new block if there are not enough
static void
ensureFreeSpace(int size_w)
{
    if (current_block != NULL &&
        (current_block->free + size_w
            < current_block->start + current_block->blocks * BLOCK_SIZE_W)) {
        // still has enough space, no-op
        return;
    }
    bdescr *old_block = current_block;
    W_ n_blocks = (W_)BLOCK_ROUND_UP(size_w*sizeof(W_)) / BLOCK_SIZE;
    current_block = allocGroup_lock(n_blocks);
    current_block->flags |= BF_STATIC;
    current_block->link = old_block;
    static_blocks += n_blocks;
}

// Invariant: concurrent calls to processStaticClosures should
// not occur until after initStaticClosures finishes.
void
initStaticClosures(void)
{
    if (current_block == NULL) {
        int size_w;

#ifdef THREADED_RTS
        initMutex(&static_closures_mutex);
#endif

        // ToDo: do a proper block size check
        // ToDo: does this need to get tagged?
        size_w = (MAX_CHARLIKE-MIN_CHARLIKE+1) * sizeofW(StgIntCharlikeClosure);
        ensureFreeSpace(size_w);
        memcpy(current_block->free,
               stg_CHARLIKE_static_closure,
               size_w*sizeof(W_));
        IF_DEBUG(sanity,
            memset(stg_CHARLIKE_static_closure, 0xDD, size_w*sizeof(W_)));
        stg_CHARLIKE_static_closure_ind =
            (StgIntCharlikeClosure*)current_block->free;
        current_block->free += size_w;

        size_w = (MAX_INTLIKE-MIN_INTLIKE+1) * sizeofW(StgIntCharlikeClosure);
        ensureFreeSpace(size_w);
        memcpy(current_block->free,
               stg_INTLIKE_static_closure,
               size_w*sizeof(W_));
        IF_DEBUG(sanity,
            memset(stg_INTLIKE_static_closure, 0xDD, size_w*sizeof(W_)));
        stg_INTLIKE_static_closure_ind =
            (StgIntCharlikeClosure*)current_block->free;
        current_block->free += size_w;
    }

    processStaticClosures();
}

void
processStaticClosures()
{
    StaticClosureInds *sci, *next_sci, *base_sci;

    // XXX Initialization code should take the lock too...
    ACQUIRE_LOCK(&static_closures_mutex);

    base_sci = SCI_LIST;
    SCI_LIST = NULL;

    // copy stuff (not updating fields)

    // Before:
    //      foo_static_closure_ind => foo_static_closure + tag
    //          foo_static_closure => ... | foo_static_closure_ind | ...
    // After:
    //      foo_static_closure_ind => dyn_addr + tag
    //          foo_static_closure => 0xDDDDDDDD DDDDDDDD (with -DS)
    //                    dyn_addr => ... | foo_static_closure_ind | ...

    // (Keep the lock due to access to the block)

    for (sci = base_sci; sci != NULL; sci = sci->link) {
        StgClosure **pp;
        for (pp = sci->start; pp < sci->end; pp++) {
            StgClosure *p = *pp;
            W_ size_w;
            ASSERT(LOOKS_LIKE_CLOSURE_PTR(p));
            StgWord tag = GET_CLOSURE_TAG(p);
            p = UNTAG_CLOSURE(p);
            const StgInfoTable *info = get_itbl(p);
            // Dicey business! Check mkStaticClosureFields for
            // the sordid details
            switch (info->type) {
            case CONSTR_STATIC:
                // info_table
                // {payload}
                // static_link
                size_w = sizeW_fromITBL(info) + 1;
                break;
            case FUN_STATIC:
                if (info->srt_bitmap != 0) {
                    // info_table
                    // static_link
                    size_w = 2;
                } else {
                    // info_table
                    size_w = 1;
                    // Nota bene: there may be a little bit of slop
                    // here, if the code generator tacked on a
                    // static_link when it didn't need to
                }
                break;
            case CONSTR_NOCAF_STATIC:
                // info_table
                // {payload}
                size_w = sizeW_fromITBL(info);
                break;
            case THUNK_STATIC:
                // info_table
                // indirectee
                // static_link
                // saved_info
                size_w = 4;
                break;
            case IND_STATIC:
                // Laid out explicitly!
                size_w = sizeofW(StgIndStatic);
                break;
            default:
                barf("initStaticClosures: strange closure type %d",
                     (int)(info->type));
            }
            ensureFreeSpace(size_w);
            memcpy(current_block->free, p, size_w*sizeof(W_));
            IF_DEBUG(sanity, memset(p, 0xDD, size_w*sizeof(W_)));
            *pp = TAG_CLOSURE(tag, (StgClosure*)current_block->free);
            current_block->free += size_w;
        }
    }

    RELEASE_LOCK(&static_closures_mutex);

    // update fields

    // Before:
    //      foo_static_closure_ind => dyn_addr + tag
    //                    dyn_addr => ... | foo_static_closure_ind | ...
    // After:
    //      foo_static_closure_ind => dyn_addr + tag
    //                    dyn_addr => ... | dyn_addr + tag | ...

    for (sci = base_sci; sci != NULL; sci = next_sci) {
        next_sci = sci->link;
        sci->link = NULL;
        StgClosure **pp;
        for (pp = sci->start; pp < sci->end; pp++) {
            StgClosure *p = UNTAG_CLOSURE(*pp);
            ASSERT(LOOKS_LIKE_CLOSURE_PTR(p));
            const StgInfoTable *info = get_itbl(p);
            switch (info->type) {
            case FUN_STATIC:
            case THUNK_STATIC:
            case CONSTR_NOCAF_STATIC:
              {
                ASSERT(info->layout.payload.ptrs == 0);
                break;
              }
            case CONSTR_STATIC:
              {
                StgClosure **q, **end;

                end = ((StgClosure**)p->payload) + info->layout.payload.ptrs;
                for (q = p->payload; q < end; q++) {
                    initialize_field(q);
                }
                break;
              }
            case IND_STATIC:
                // ToDo: just short-circuit it
                initialize_field(&((StgInd *)p)->indirectee);
                break;
            default:
                barf("initStaticClosures: strange closure type %d",
                     (int)(info->type));
            }
        }
        sci->start = sci->end = NULL;
    }
}
