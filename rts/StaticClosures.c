/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2013
 *
 * Responsible for copying static closures into proper blocks so that
 * bdescr works.
 *
 * ---------------------------------------------------------------------------*/

#include "Rts.h"
#include "Prelude.h"
#include "StaticClosures.h"
#include "ResourceLimits.h"
#include "sm/Storage.h"

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
static bdescr* ensureFreeSpace(bdescr **, int);
static W_ n_global_blocks = 0;
static bdescr *global_block = NULL;

W_ countStaticBlocks() {
    return n_global_blocks;
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

#ifdef DEBUG

// Helper debug function for when you're in GDB.
// Calculate the arguments by running 'objdump -h executable'
// and look for the 'staticclosureinds' section:
//
//Idx Name              SIZE      VMA               LMA               File off  Algn
// 25 staticclosureinds 00003090  0000000000742748  0000000000742748  00142748  2**3
//
// Then run checkStaticClosures(SIZE, VMA) after initStaticClosures
// to check if initialization was good.  The way we test for this is
// looking for any pointers which are still pointing into the
// indirections (this is how it is initialized).
void
checkStaticClosures(W_ size_b, StgClosure **section_start) {
    StgClosure **pp;
    StgClosure **section_end = (StgClosure**)((W_)section_start + size_b);
    W_ payload_size;
    for (pp = section_start; pp < section_end; pp += sizeofW(StgStaticClosureDesc) + payload_size) {
        StgClosure *p = UNTAG_CLOSURE(*pp);
        // Not perfect, but will segfault if it's not actually a block
        ASSERT(!HEAP_ALLOCED(p));
        payload_size = 0;
        // TODO: sanity check tagging
        const StgInfoTable *info = get_itbl(p);
        // XXX: It would better if we can process all closure types
        // uniformly
        switch (info->type) {
        case FUN_STATIC:
        case THUNK_STATIC:
        case CONSTR_STATIC:
        case CONSTR_NOCAF_STATIC:
          {
            StgClosure **q, **end;

            payload_size = info->layout.payload.ptrs + info->layout.payload.nptrs;
            end = ((StgClosure**)p->payload) + info->layout.payload.ptrs;
            for (q = p->payload; q < end; q++) {
                ASSERT(!(*q >= (StgClosure*)section_start && *q < (StgClosure*)section_end));
            }
            break;
          }
        case IND_STATIC:
            payload_size = 1;
            ASSERT(!(((StgInd*)p)->indirectee >= (StgClosure*)section_start && ((StgInd*)p)->indirectee < (StgClosure*)section_end));
            break;
        default:
            barf("checkStaticClosures: strange closure type %d", (int)(info->type));
        }
    }
}

#endif

// Ensure there are size_w words available in the current block; allocating
// a new block if there are not enough
static bdescr*
ensureFreeSpace(bdescr **current_block_p, int size_w)
{
    bdescr *current_block = *current_block_p;
    if (current_block != NULL &&
        (current_block->free + size_w
            < current_block->start + current_block->blocks * BLOCK_SIZE_W)) {
        // still has enough space, no-op
        return current_block;
    }
    ASSERT(RC_MAIN != NULL);
    W_ n_blocks = (W_)BLOCK_ROUND_UP(size_w*sizeof(W_)) / BLOCK_SIZE;
    ASSERT(n_blocks < BLOCKS_PER_MBLOCK);
    ACQUIRE_SM_LOCK;
    bdescr *new_block = forceAllocGroupFor(n_blocks, RC_MAIN);
    RELEASE_SM_LOCK;
    new_block->flags |= BF_STATIC;
    // to handle closure tables, mark all other blocks as BF_STATIC too
    bdescr *bd;
    W_ i;
    for (i=1, bd=new_block+1; i < n_blocks; i++, bd++) {
        bd->flags |= BF_STATIC;
    }
    new_block->link = current_block;
    *current_block_p = new_block;
    // special case for global blocks
    if (&global_block == current_block_p) {
        n_global_blocks += n_blocks;
    }
    return new_block;
}

// Invariant: concurrent calls to processStaticClosures should
// not occur until after initStaticClosures finishes.
void
initStaticClosures(void)
{
    if (global_block == NULL) {
        int size_w;
        StgIntCharlikeClosure *p;

#ifdef THREADED_RTS
        initMutex(&static_closures_mutex);
#endif

        // ToDo: does this need to get tagged?
        size_w = (MAX_CHARLIKE - MIN_CHARLIKE + 1) * sizeofW(StgIntCharlikeClosure);
        ensureFreeSpace(&global_block, size_w);
        StgWord c;
        for (p = (StgIntCharlikeClosure*)global_block->free, c = MIN_CHARLIKE;
                c <= MAX_CHARLIKE; c++, p++) {
            p->header.info = Czh_static_info;
#ifdef PROFILING
            p->header.prof.ccs = CCS_DONT_CARE;
            p->header.prof.ldvw = 0;
#endif
            p->data = c;
        }
        stg_CHARLIKE_static_closure_ind = (StgIntCharlikeClosure*)global_block->free;
        global_block->free += size_w;
        ASSERT((StgWord*)p == global_block->free);

        size_w = (MAX_INTLIKE - MIN_INTLIKE + 1) * sizeofW(StgIntCharlikeClosure);
        ensureFreeSpace(&global_block, size_w);
        StgInt i;
        for (p = (StgIntCharlikeClosure*)global_block->free, i = MIN_INTLIKE;
                i <= MAX_INTLIKE; i++, p++) {
            p->header.info = Izh_static_info;
#ifdef PROFILING
            p->header.prof.ccs = CCS_DONT_CARE;
            p->header.prof.ldvw = 0;
#endif
            p->data = (StgWord)i;
        }
        stg_INTLIKE_static_closure_ind = (StgIntCharlikeClosure*)global_block->free;
        global_block->free += size_w;
        ASSERT((StgWord*)p == global_block->free);
    }

    processStaticClosures(SCI_LIST, &global_block);
    SCI_LIST = NULL;

    // deferred initialization
    RC_MAIN->listeners = END_LISTENER_LIST;
}

void
processStaticClosures(StaticClosureInds *base_sci, bdescr **current_block_p)
{
    allocateStaticClosures(base_sci, current_block_p);
    updateStaticClosureFields(base_sci);
}

void
allocateStaticClosures(StaticClosureInds *base_sci, bdescr **current_block_p)
{
    if (current_block_p == NULL) current_block_p = &global_block;

    // XXX Initialization code should take the lock too...
    ACQUIRE_LOCK(&static_closures_mutex);

    // copy stuff (not updating fields)

    // Before:
    //      foo_static_closure_ind => info table + tag
    //                                (ccs if profiling)
    //                                payload
    // After:
    //      foo_static_closure_ind => dyn_addr + tag
    //                                0xDDDDDDDD DDDDDDDD (with -DS)
    //                    dyn_addr => info table | ... | foo_static_closure_ind | ...

    // (Keep the lock due to access to the block)

    StaticClosureInds *sci;
    for (sci = base_sci; sci != NULL; sci = sci->link) {
        StgClosure **pp; // for easier pointer arithmetic; technically it's StgStaticClosureDesc*
        W_ payload_size;
        for (pp = sci->start; pp < sci->end; pp += sizeofW(StgStaticClosureDesc) + payload_size) {
            StgStaticClosureDesc *p = (StgStaticClosureDesc*)pp;
            StgWord tag = GET_CLOSURE_TAG((StgClosure*)p->t.tagged_info);
            // XXX could be bad if the alignment is not good enough
            const StgInfoTable *info_ptr = (StgInfoTable*)UNTAG_CLOSURE((StgClosure*)p->t.tagged_info);
            ASSERT(LOOKS_LIKE_INFO_PTR((StgWord)info_ptr));
            const StgInfoTable *info = INFO_PTR_TO_STRUCT(info_ptr);

            W_ size_w = 0; // sizeof(q)
            payload_size = 0; // the p payload, not the q payload
            rtsBool needsPadding = rtsFalse;
            rtsBool needsStaticLink = rtsFalse;
            rtsBool needsSavedInfo = rtsFalse;
            // XXX: It would better if we can process all closure types
            // uniformly
            switch (info->type) {
            case CONSTR_STATIC:
                needsStaticLink = rtsTrue;
                size_w += 2;
                // fallthrough
            case CONSTR_NOCAF_STATIC:
                // {header}
                // {payload}
                // static_link if has CAFs
                size_w += sizeW_fromITBL(info);
                payload_size = info->layout.payload.ptrs + info->layout.payload.nptrs;
                break;
            case FUN_STATIC:
                // {header}
                // static_link?
                size_w += sizeofW(StgHeader);
                if (info->srt_bitmap != 0) {
                    needsStaticLink = rtsTrue;
                    size_w += 2;
                }
                // TODO: ASSERT that itbl payload is empty
                break;
            case THUNK_STATIC:
                // CAFs must have consistent layout, regardless of whether they
                // are actually updatable or not.  The layout of a CAF is:
                //
                //        3 saved_info
                //        2 static_link
                //        1 indirectee
                //        0 {header}
                //
                // the static_link and saved_info fields must always be in the
                // same place.
                size_w += sizeofW(StgThunkHeader) + 3;
                needsPadding = rtsTrue;
                needsStaticLink = rtsTrue;
                needsSavedInfo = rtsTrue;
                // TODO: ASSERT that itbl payload is empty
                break;
            case IND_STATIC:
                size_w += sizeofW(StgIndStatic);
                payload_size = 1;
                needsStaticLink = rtsTrue;
                needsSavedInfo = rtsTrue;
                break;
            default:
                barf("initStaticClosures: strange closure type %d", (int)(info->type));
            }
            bdescr *current_block = ensureFreeSpace(current_block_p, size_w);

            StgClosure *q = (StgClosure*)current_block->free;
            q->header.info = info_ptr;
#ifdef PROFILING
            q->header.prof.ccs = p->ccs;
            IF_DEBUG(sanity, memset(&p->ccs, 0xDD, sizeof(W_)));
            q->header.prof.ldvw = 0;
#endif
            W_ i = 0;
            ASSERT(!needsPadding || payload_size == 0);
            for (; i < payload_size; i++) {
                q->payload[i] = p->payload[i];
                IF_DEBUG(sanity, memset(&p->payload[i], 0xDD, sizeof(W_)));
            }
            if (needsPadding) {
                q->payload[i++] = 0;
            }
            if (needsStaticLink) {
                // For a static constructor which has no CAF refs, we set the
                // static link field to a non-zero value so the garbage
                // collector will ignore it.
                q->payload[i++] = (StgClosure*)(W_)(info->type == CONSTR_NOCAF_STATIC ? 1 : 0);
                // static_ind field, records p's location
                q->payload[i++] = (StgClosure*)p;
            }
            if (needsSavedInfo) {
                q->payload[i++] = 0;
            }
            current_block->free += size_w;
            ASSERT((StgClosure*)&q->payload[i] == (StgClosure*)current_block->free);
            p->t.dest = TAG_CLOSURE(tag, q);
        }
        ASSERT(pp == sci->end);
    }

    RELEASE_LOCK(&static_closures_mutex);
}

void
updateStaticClosureFields(StaticClosureInds *base_sci)
{
    StaticClosureInds *sci, *next_sci;

    // Before:
    //      foo_static_closure_ind => dyn_addr + tag
    //                    dyn_addr => ... | foo_static_closure_ind | ...
    // After:
    //      ooo_static_closure_ind => dyn_addr + tag
    //                    dyn_addr => ... | dyn_addr + tag | ...

    for (sci = base_sci; sci != NULL; sci = next_sci) {
        next_sci = sci->link;
        sci->link = NULL;
        StgClosure **pp;
        W_ payload_size;
        for (pp = sci->start; pp < sci->end; pp += sizeofW(StgStaticClosureDesc) + payload_size) {
            StgClosure *p = UNTAG_CLOSURE(*pp);
            ASSERT(LOOKS_LIKE_CLOSURE_PTR(p));
            const StgInfoTable *info = get_itbl(p);
            payload_size = 0;
            // XXX: It would better if we can process all closure types
            // uniformly
            switch (info->type) {
            case FUN_STATIC:
            case THUNK_STATIC:
                ASSERT(info->layout.payload.ptrs == 0);
                break;
            case CONSTR_NOCAF_STATIC:
                ASSERT(info->layout.payload.ptrs == 0);
                // fallthrough
            case CONSTR_STATIC:
              {
                StgClosure **q, **end;

                payload_size = info->layout.payload.ptrs + info->layout.payload.nptrs;
                end = ((StgClosure**)p->payload) + info->layout.payload.ptrs;
                for (q = p->payload; q < end; q++) {
                    initialize_field(q);
                }
                break;
              }
            case IND_STATIC:
                // ToDo: just short-circuit it
                initialize_field(&((StgInd *)p)->indirectee);
                payload_size = 1;
                break;
            default:
                barf("initStaticClosures: strange closure type %d", (int)(info->type));
            }
        }
        sci->start = sci->end = NULL;
    }
}
