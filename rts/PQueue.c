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
    return q;
}

void
freePQueue (PQueue *q)
{
    stgFree(q->elements);
    stgFree(q);
}

void
iteratePQueue(PQueue *q, void (*fp)(StgTSO *e)) {
    nat i;
    // 0 1 2 (size = 3, deferred = 0)
    //   1 2 (size = 2, deferred = 1)
    for (i = q->deferred; i < q->size + q->deferred; i++) {
        fp(q->elements[i]);
    }
}

void
markPQueue(PQueue *q, evac_fn evac, void *user) {
    nat i;
    for (i = q->deferred; i < q->size + q->deferred; i++) {
        evac(user, (StgClosure **)&q->elements[i]);
    }
}

void
truncatePQueue(PQueue *q) {
    q->size = 0;
}

void
growPQueue(PQueue *q) {
    int esz = q->capacity * sizeof(StgClosurePtr);
    void ** nelements = stgMallocBytes(2 * esz, "insertPQueue: elements");
    memcpy(/*dst*/nelements, q->elements, esz);
    stgFree(q->elements);
    q->elements = nelements;
    q->capacity *= 2;
}
