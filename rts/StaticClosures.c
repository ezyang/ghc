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

StaticClosureInds *SCI_LIST = NULL;

// very similar to the scavenge code

static void initialize_field(StgClosure **p);
static void initialize_closure_large_srt(StgLargeSRT*);
static void initialize_closure_srt(StgClosure**, nat srt_bitmap);

void
initialize_field(StgClosure **p)
{
      StgClosure *q = *p;
      StgWord tag = GET_CLOSURE_TAG(q);
      // guaranteed to be something else static
      *p = TAG_CLOSURE(tag, *(StgClosure**)UNTAG_CLOSURE(q));
      // XXX happens to work because nothing changes
}

void
initialize_closure_large_srt (StgLargeSRT* large_srt)
{
    nat i, b, size;
    StgWord bitmap;
    StgClosure **p;

    b = 0;
    bitmap = large_srt->l.bitmap[b];
    size   = (nat)large_srt->l.size;
    p      = (StgClosure **)large_srt->srt;
    for (i = 0; i < size; ) {
        if ((bitmap & 1) != 0) {
            initialize_field(p);
        }
        i++;
        p++;
        if (i % BITS_IN(W_) == 0) {
            b++;
            bitmap = large_srt->l.bitmap[b];
        } else {
            bitmap = bitmap >> 1;
        }
    }
}

void
initialize_closure_srt (StgClosure **srt, nat srt_bitmap)
{
  nat bitmap;
  StgClosure **p;

  bitmap = srt_bitmap;
  p = srt;

  if (bitmap == (StgHalfWord)(-1)) {  
      initialize_closure_large_srt( (StgLargeSRT *)srt );
      return;
  }

  while (bitmap != 0) {
      if ((bitmap & 1) != 0) {
          // maybe need to do something for dlls
          initialize_field(p);
      }
      p++;
      bitmap = bitmap >> 1;
  }
}

void
initStaticClosures(void)
{
    // XXX stub for now
    StaticClosureInds *sci;
    for (sci = SCI_LIST; sci != NULL; sci = sci->link) {
        StgClosure **pp;
        for (pp = sci->start; pp < sci->end; pp++) {
            StgClosure *p = *pp;
            ASSERT(GET_CLOSURE_TAG(p) == 1);
            *pp = UNTAG_CLOSURE(p);
            const StgInfoTable *info = get_itbl(p);
            switch (info->type) {
            case THUNK_STATIC:
              {
                StgThunkInfoTable *thunk_info = itbl_to_thunk_itbl(info);
                initialize_closure_srt((StgClosure **)GET_SRT(thunk_info), thunk_info->i.srt_bitmap);
                break;
              }
            case FUN_STATIC:
              {
                StgFunInfoTable *fun_info = itbl_to_fun_itbl(info);
                initialize_closure_srt((StgClosure **)GET_FUN_SRT(fun_info), fun_info->i.srt_bitmap);
                break;
              }
            case CONSTR_STATIC:
              {
                StgPtr q, next;
                next = (P_)p->payload + info->layout.payload.ptrs;
                // evacuate the pointers 
                for (q = (P_)p->payload; q < next; q++) {
                    initialize_field((StgClosure **)q);
                }
                break;
              }
            default:
                barf("evacuate(static): strange closure type %d", (int)(info->type));
            }
        }
    }
}
