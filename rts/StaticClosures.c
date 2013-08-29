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

// very similar to the scavenge code

static void initialize_field(StgClosure **p);
static void addBlock(void);
static W_ static_blocks = 0;
static bdescr *current_block;

W_ countStaticBlocks() {
    return static_blocks;
}

void
initialize_field(StgClosure **p)
{
    // The field of a static closure starts off as a tagged pointer to
    // the *indirection*.  After we rewrite it, it is now just a tagged
    // pointer to the destination of the indirection (thus the untag/tag
    // pattern.)
    StgClosure *q = *p;
    StgWord tag = GET_CLOSURE_TAG(q);
    StgClosure *r = UNTAG_CLOSURE(*(StgClosure**)UNTAG_CLOSURE(q));
    ASSERT(LOOKS_LIKE_CLOSURE_PTR(r));
    *p = TAG_CLOSURE(tag, r);
}

void
checkStaticClosures(StgClosure **section_start, StgClosure **section_end) {
    StgClosure **pp;
    for (pp = section_start; pp < section_end; pp++) {
        StgClosure *p = *pp;
        ASSERT(GET_CLOSURE_TAG(p) == 0);
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

static void
addBlock(void)
{
    bdescr *old_block = current_block;
    current_block = allocBlock_lock();
    current_block->link = old_block;
    static_blocks++;
}

void
initStaticClosures(void)
{
    int size_w;

    // ToDo: do a proper block size check
    addBlock();
    size_w = (MAX_CHARLIKE - MIN_CHARLIKE + 1) * sizeofW(StgIntCharlikeClosure);
    memcpy(current_block->free, stg_CHARLIKE_static_closure, size_w*sizeof(W_));
    stg_CHARLIKE_static_closure_ind = stg_CHARLIKE_static_closure;
    current_block->free += size_w;
    ASSERT(current_block->free <= current_block->start + BLOCK_SIZE_W);

    addBlock();
    size_w = (MAX_INTLIKE - MIN_INTLIKE + 1) * sizeofW(StgIntCharlikeClosure);
    memcpy(current_block->free, stg_INTLIKE_static_closure, size_w*sizeof(W_));
    stg_INTLIKE_static_closure_ind = stg_INTLIKE_static_closure;
    current_block->free += size_w;
    ASSERT(current_block->free <= current_block->start + BLOCK_SIZE_W);

    processStaticClosures();
}

void
processStaticClosures()
{
    StaticClosureInds *sci, *next_sci, *base_sci;

    base_sci = SCI_LIST;
    SCI_LIST = NULL;

    // copy stuff (not updating fields)

    for (sci = base_sci; sci != NULL; sci = sci->link) {
        StgClosure **pp;
        for (pp = sci->start; pp < sci->end; pp++) {
            StgClosure *p = *pp;
            W_ size_w;
            ASSERT(LOOKS_LIKE_CLOSURE_PTR(p));
            ASSERT(GET_CLOSURE_TAG(p) == 1);
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
            // we can do a sanity check for all except the last closure
            ASSERT(pp+1 == sci->end
                    // use the packing of closures together as the test...
                    || UNTAG_CLOSURE(*(pp+1)) == p + size_w
                    // ...but allow FUN_STATIC to be a little sloppy
                    || (info->type == FUN_STATIC && size_w == 1 &&
                            (*((W_*)p+1) & ~1) == 0));
            // ToDo: relax this restriction
            ASSERT(size_w < BLOCK_SIZE_W);
            if (current_block->free  + size_w >=
                current_block->start + BLOCK_SIZE_W) {
                // out of space, make a new current_block
                addBlock();
            }
            memcpy(current_block->free, p, size_w*sizeof(W_));
            current_block->free += size_w;
        }
    }

    // update fields
    // ToDo: Could make this faster by just walking over the static blocks

    for (sci = base_sci; sci != NULL; sci = next_sci) {
        next_sci = sci->link;
        sci->link = NULL;
        StgClosure **pp;
        for (pp = sci->start; pp < sci->end; pp++) {
            StgClosure *p = *pp;
            ASSERT(LOOKS_LIKE_CLOSURE_PTR(p));
            ASSERT(GET_CLOSURE_TAG(p) == 1);
            p = UNTAG_CLOSURE(p);
            *pp = p;
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
