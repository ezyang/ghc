/*
 * Priority queue data structure (not concurrent).
 *
 * Classic undergraduate implementation of a Heap.
 */

#include "PosixSource.h"
#include "Rts.h"

#include "RtsUtils.h"
#include "PQueue.h"

PQueue *
newPQueue (nat size)
{
    StgWord realsize;
    PQueue *q;
    realsize = roundUp2(size);
    q = (PQueue*) stgMallocBytes(sizeof(PQueue), "newPQueue");
    int sz = realsize * sizeof(StgClosurePtr);
    q->elements = stgMallocBytes(sz, "newPQueue: elements");
    q->keys = stgMallocBytes(realsize * sizeof(StgWord64), "newPQueue: keys");
    q->capacity = realsize;
    q->size = 0;
    return q;
}

void
freePQueue (PQueue *q)
{
    stgFree(q->elements);
    stgFree(q->keys);
    stgFree(q);
}

#define PARENT(i) (((i)-1)/2)
#define LEFT(i)   (2*(i)+1)
#define RIGHT(i)  (2*(i)+2)

void
insertPQueue(PQueue *q, void *elem, StgWord64 key)
{
    if (q->size == q->capacity) {
        // resize it
        int esz = q->capacity * sizeof(StgClosurePtr);
        void ** nelements = stgMallocBytes(2 * esz, "insertPQueue: elements");
        memcpy(/*dst*/nelements, q->elements, esz);
        stgFree(q->elements);
        q->elements = nelements;
        int ksz = q->capacity * sizeof(StgWord64);
        void ** nkeys = stgMallocBytes(2 * ksz, "insertPQueue: keys");
        memcpy(/*dst*/nkeys, q->keys, ksz);
        stgFree(q->keys);
        q->keys = nkeys;
        q->capacity *= 2;
    }
    nat i;
    for (i = q->size; i > 0 && q->keys[PARENT(i)] > key; i = PARENT(i)) {
        q->elements[i] = q->elements[PARENT(i)];
        q->keys[i] = q->keys[PARENT(i)];
    }
    q->elements[i] = elem;
    q->keys[i] = key;
    q->size++;
}

void *
peekMinPQueue(PQueue *q, StgWord64 *oldKey) {
    if (q->size == 0) {
        return NULL;
    }
    if (oldKey != NULL) {
        *oldKey = q->keys[0];
    }
    return q->elements[0];
}

void *
deleteMinPQueue(PQueue *q, StgWord64 *oldKey) {
    if (q->size == 0) {
        return NULL;
    }
    void *min = q->elements[0];
    if (oldKey != NULL) {
        *oldKey = q->keys[0];
    }
    q->size--;
    void *last = q->elements[q->size];
    StgWord64 lastk = q->keys[q->size];
    nat c, i;
    for (i = 0; LEFT(i) < q->size; i = c) {
        if (LEFT(i) != q->size && q->keys[LEFT(i)] > q->keys[RIGHT(i)]) {
            c = RIGHT(i); // right exists and wins
        } else {
            c = LEFT(i); // only had left node, or left wins
        }
        if (lastk > q->keys[c]) {
            q->keys[i] = q->keys[c];
            q->elements[i] = q->elements[c];
        } else {
            break;
        }
    }
    q->elements[i] = last;
    q->keys[i] = lastk;
    // XXX implementing properly amortized downsizing
    return min;
}

void
truncatePQueue(PQueue *q) {
    q->size = 0;
}

#undef PARENT
#undef LEFT
#undef RIGHT
