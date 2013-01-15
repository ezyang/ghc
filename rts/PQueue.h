/*
 * Priority queue data structure (not concurrent)
 */

#ifndef PQUEUE_H
#define PQUEUE_H

typedef struct PQueue_ {
    // size of the heap array
    StgWord size;
    // capacity of the heap array
    StgWord capacity;
    // the elements array
    void ** elements;
    // the keys array
    StgWord64 * keys;
} PQueue;

PQueue * newPQueue(nat size);
void freePQueue(PQueue *q);

void * deleteMinPQueue(PQueue *q, StgWord64 *oldKey);
void * peekMinPQueue(PQueue *q, StgWord64 *oldKey);
void insertPQueue(PQueue *q, void *elem, StgWord64 key);
void truncatePQueue(PQueue *q);

#endif // PQUEUE_H
