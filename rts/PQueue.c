/*
 * Priority queue data structure (not concurrent).
 *
 * Classic undergraduate implementation of a Heap.
 */

#include "PosixSource.h"
#include "Rts.h"

#include "RtsUtils.h"
#include "PQueue.h"
#include "sm/GC.h"

PQueue *
newPQueue (nat size)
{
    StgWord realsize;
    PQueue *q;
    realsize = roundUp2(size);
    q = (PQueue*) stgMallocBytes(sizeof(PQueue), "newPQueue");
    int sz = realsize * sizeof(StgClosurePtr);
    q->elements = stgMallocBytes(sz, "newPQueue: elements");
    q->capacity = realsize;
    q->size = 0;
    q->deferred = 0;
    ASSERT_PQUEUE_INVARIANTS(q);
    return q;
}

void
freePQueue (PQueue *q)
{
    ASSERT_PQUEUE_INVARIANTS(q);
    stgFree(q->elements);
    stgFree(q);
}

#define PARENT(i) (((i)-1)/2)
#define LEFT(i)   (2*(i)+1)
#define RIGHT(i)  (2*(i)+2)

void
iteratePQueue(PQueue *q, void (*fp)(StgTSO *e))
{
    nat i;
    for (i = q->deferred; i < q->size + q->deferred; i++) {
        fp(q->elements[i]);
    }
    ASSERT_PQUEUE_INVARIANTS(q);
}

void
markPQueue(PQueue *q, evac_fn evac, void *user)
{
    nat i;
    for (i = q->deferred; i < q->size + q->deferred; i++) {
        evac(user, (StgClosure **)&q->elements[i]);
    }
}

void checkHeapProperty(PQueue*);
void checkHeapProperty(PQueue *q)
{
    ASSERT_PQUEUE_INVARIANTS(q);
    nat i;
    for (i = q->deferred ? 3 : 1; i < q->size + q->deferred; i++) {
        ASSERT(q->elements[i]->ss_pass <= q->elements[PARENT(i)]->ss_pass);
    }
}

void upHeap(PQueue*, StgTSO*);
void
upHeap(PQueue *q, StgTSO* last)
{
    // q should look like this:
    //
    // elements = [ _ 1 2 3 4 ... (n-1) ]
    //     last = 0
    //     size = n
    //
    // Morally, last == q->elements[0], but for optimization reasons,
    // this may not be true.
    //
    // last violates heap property with 1 and/or 2; but everyone
    // else has the heap property; this function restores the heap property.
    ASSERT(!q->deferred);
    StgWord64 lastk = last->ss_pass;
    nat c, i;
    for (i = 0; LEFT(i) < q->size; i = c) {
        if (LEFT(i) != q->size - 1 && q->elements[LEFT(i)]->ss_pass > q->elements[RIGHT(i)]->ss_pass) {
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
    IF_DEBUG(sanity, checkHeapProperty(q));
}

void
insertPQueue(PQueue *q, StgTSO *elem)
{
    StgWord64 key = elem->ss_pass;
    if (q->size == q->capacity) {
        // resize it
        int esz = q->capacity * sizeof(StgClosurePtr);
        void ** nelements = stgMallocBytes(2 * esz, "insertPQueue: elements");
        memcpy(/*dst*/nelements, q->elements, esz);
        stgFree(q->elements);
        q->elements = nelements;
        q->capacity *= 2;
    }
    q->size++;
    if (q->deferred) {
        q->deferred = 0;
        upHeap(q, elem);
    } else {
        nat i;
        for (i = q->size - 1; i > 0 && q->elements[PARENT(i)]->ss_pass > key; i = PARENT(i)) {
            q->elements[i] = q->elements[PARENT(i)];
        }
        q->elements[i] = elem;
    }
    ASSERT_PQUEUE_INVARIANTS(q);
}

void *
peekMinPQueue(PQueue *q)
{
    if (q->size == 0) {
        return NULL;
    }
    if (q->deferred) {
        q->deferred = 0;
        upHeap(q, q->elements[q->size]);
    }
    ASSERT_PQUEUE_INVARIANTS(q);
    return q->elements[0];
}

void *
deleteMinPQueue(PQueue *q)
{
    if (q->size == 0) {
        return NULL;
    }
    if (q->deferred) {
        q->deferred = 0;
        upHeap(q, q->elements[q->size]);
    }
    q->deferred = 1;
    q->size--;
    // XXX implementing properly amortized downsizing
    StgTSO *min = q->elements[0];
#ifdef DEBUG
    q->elements[0] = NULL; // for debugging
#endif
    ASSERT_PQUEUE_INVARIANTS(q);
    return min;
}

void
truncatePQueue(PQueue *q)
{
    q->size = 0;
    q->deferred = 0;
    ASSERT_PQUEUE_INVARIANTS(q);
}

#undef PARENT
#undef LEFT
#undef RIGHT
