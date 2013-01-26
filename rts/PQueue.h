/*
 * Priority queue data structure (not concurrent)
 */

#ifndef PQUEUE_H
#define PQUEUE_H

#include "sm/GC.h"

typedef struct PQueue_ {
    // number of elements in the heap array
    StgWord size;
    // capacity of the heap array
    StgWord capacity;
    // the elements array
    StgTSO **elements;
    // - if deferred = 0, elements is an ordinary zero-indexed heap
    // occupying elements 0 ... (size-1)
    // - if deferred = 1, then elements is a zero-indexed heap with
    // a "hole" at zero; valid elements live at 1 ... size.
    // Modulo the hole, the heap property is still obeyed.
    int deferred;
    // min element (only valid when deferred == 1)
    StgTSO *min;
} PQueue;

#define ASSERT_PQUEUE_INVARIANTS(p) \
    ASSERT((p)->size >= 0); \
    ASSERT((p)->capacity > 0); \
    ASSERT((p)->size <= (p)->capacity); \
    ASSERT(!(p)->deferred || (p)->elements[0] == NULL);

PQueue * newPQueue(nat size);
void freePQueue(PQueue *q);

void * deleteMinPQueue(PQueue *q);
void * peekMinPQueue(PQueue *q);
void insertPQueue(PQueue *q, StgTSO *elem);
void truncatePQueue(PQueue *q);
void iteratePQueue(PQueue *q, void (*fp)(StgTSO *e));
void markPQueue(PQueue *q, evac_fn evac, void *user);

#endif // PQUEUE_H
