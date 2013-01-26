/*
 * Priority queue data structure (not concurrent)
 */

#ifndef PQUEUE_H
#define PQUEUE_H

#include "sm/GC.h"

#define PARENT(i) (((i)-1)/2)
#define LEFT(i)   (2*(i)+1)
#define RIGHT(i)  (2*(i)+2)

typedef struct PQueue_ {
    // size of the heap array
    StgWord size;
    // capacity of the heap array
    StgWord capacity;
    // the elements array
    StgTSO **elements;
    // deferred?
    int deferred;
} PQueue;

PQueue * newPQueue(nat size);
void freePQueue(PQueue *q);

EXTERN_INLINE void upHeap(PQueue*, StgTSO*);
EXTERN_INLINE void
upHeap(PQueue *q, StgTSO *last)
{
    StgWord64 lastk = last->ss_pass;
    nat c, i;
    for (i = 0; LEFT(i) < q->size; i = c) {
        if (LEFT(i) != q->size && q->elements[LEFT(i)]->ss_pass > q->elements[RIGHT(i)]->ss_pass) {
            c = RIGHT(i); // right exists and wins
        } else {
            c = LEFT(i); // only had left node, or left wins
        }
        if (lastk > q->elements[c]->ss_pass) {
            q->elements[i] = q->elements[c];
        } else {
            break;
        }
    }
    q->elements[i] = last;
}

EXTERN_INLINE void * deleteMinPQueue(PQueue *q);
EXTERN_INLINE void * peekMinPQueue(PQueue *q);
EXTERN_INLINE void insertPQueue(PQueue *q, StgTSO *elem);
void truncatePQueue(PQueue *q);
void iteratePQueue(PQueue *q, void (*fp)(StgTSO *e));
void markPQueue(PQueue *q, evac_fn evac, void *user);
void growPQueue(PQueue *q);

EXTERN_INLINE void
insertPQueue(PQueue *q, StgTSO *elem)
{
    StgWord64 key = elem->ss_pass;
    if (q->size == q->capacity) { growPQueue(q); }
    nat i;
    for (i = q->size; i > 0 && q->elements[PARENT(i)]->ss_pass > key; i = PARENT(i)) {
        q->elements[i] = q->elements[PARENT(i)];
    }
    q->elements[i] = elem;
    q->size++;
}

EXTERN_INLINE void *
peekMinPQueue(PQueue *q) {
    return q->elements[0];
}

EXTERN_INLINE void *
deleteMinPQueue(PQueue *q) {
    if (q->size == 0) {
        return NULL;
    }
    StgTSO *min = q->elements[0];
    q->size--;
    // XXX implementing properly amortized downsizing
    if (q->size == 0) {
        q->elements[0] = NULL; // make peekMinPQueue work
    } else {
        upHeap(q, q->elements[q->size]);
    }
    return min;
}

#undef PARENT
#undef LEFT
#undef RIGHT

#endif // PQUEUE_H
