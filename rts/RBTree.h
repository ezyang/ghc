#ifndef RBTREE_H
#define RBTREE_H

#include "Capability.h"
#include "RtsUtils.h"

// http://www.canonware.com/rb/

struct StgRB_ {
    StgRB *left, *right;
    StgTSO *head, *tail;
    int color;
}; // typedef in RtsAPI

#define RB_RED 0
#define RB_BLACK 1

#define RB_LEFT_GET(n)           ((n)->left)
#define RB_LEFT_SET(cap, n,p)    (n)->left = p;
#define RB_RIGHT_GET(n)          ((n)->right)
#define RB_RIGHT_SET(cap, n,p)   (n)->right = p;
#define RB_HEAD_GET(n)           ((n)->head)
#define RB_HEAD_SET(cap, n,p)    (n)->head = p;
#define RB_TAIL_GET(n)           ((n)->tail)
#define RB_TAIL_SET(cap, n,p)    (n)->tail = p;
// alternatively, setup a static RB_NULL closure with the appropriate
// structure and do the normal thing
#define RB_IS_RED(n)        ((n) != RB_NULL && (n)->color == RB_RED)
#define RB_IS_BLACK(n)      ((n) == RB_NULL || (n)->color == RB_BLACK)
#define RB_COLOR_GET(n)     ((n) == RB_NULL ? RB_BLACK : (n)->color)
#define RB_COLOR_RED(cap, n)     (n)->color = RB_RED;
#define RB_COLOR_BLACK(cap, n)   (n)->color = RB_BLACK;
#define RB_COLOR_SET(cap, n,c)       (n)->color = c;

int checkRBTree(StgRB *r, int forceBlack, int count, int expected);
StgRB* rbInsert(Capability *cap, StgRB **root, StgTSO *tso);
StgTSO* rbRemoveMin(Capability *cap, StgRB **root);
void rbEvacuate(evac_fn evac, void *user, StgRB* r);

// maintain a free list of nodes so we don't have to continually
// allocate them

#define RB_CHUNK (1024 * sizeof(W_) / sizeof(StgRB))

INLINE_HEADER StgRB*
rbCreateNode(Capability *cap, StgTSO *tso) {
    StgRB *n;
    if (cap->rb_free_list != RB_NULL) {
        n = cap->rb_free_list;
        cap->rb_free_list = RB_LEFT_GET(n);
    } else {
        n = (StgRB*) stgMallocBytes(RB_CHUNK * sizeof(StgRB), "rbCreateNode");
        cap->rb_free_list = n + 1;
        StgRB *p;
        for (p = cap->rb_free_list; p < n + RB_CHUNK - 1; p++) {
            p->left = p + 1;
        }
        p->left = RB_NULL;
    }
    RB_LEFT_SET(cap, n, RB_NULL);
    RB_RIGHT_SET(cap, n, RB_NULL);
    RB_HEAD_SET(cap, n, tso);
    RB_TAIL_SET(cap, n, tso);
    if (tso == END_TSO_QUEUE) {
        RB_COLOR_BLACK(cap, n);
    } else {
        RB_COLOR_RED(cap, n);
    }
    return n;
}

EXTERN_INLINE StgRB*
rbFirst(StgRB *n);

EXTERN_INLINE StgRB*
rbFirst(StgRB *n) {
    for (; RB_LEFT_GET(n) != RB_NULL; n = RB_LEFT_GET(n)) {}
    return n;
}

EXTERN_INLINE StgRB*
rbLast(StgRB *n);

EXTERN_INLINE StgRB*
rbLast(StgRB *n) {
    for (; RB_RIGHT_GET(n) != RB_NULL; n = RB_RIGHT_GET(n)) {}
    return n;
}

#endif /* RBTREE_H */
