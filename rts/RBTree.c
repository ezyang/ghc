/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2013
 *
 * Red-black trees
 *
 * The core algorithm is based off of jemalloc's red-black tree
 * implementation <http://www.canonware.com/rb/>, which has the following license:
 *
 * Copyright (C) 2002-2012 Jason Evans <jasone@canonware.com>. All rights reserved.
 * Copyright (C) 2007-2012 Mozilla Foundation.  All rights reserved.
 * Copyright (C) 2009-2012 Facebook, Inc.  All rights reserved.

 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice(s),
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice(s),
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.

 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER(S) ``AS IS'' AND ANY EXPRESS
 * OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO
 * EVENT SHALL THE COPYRIGHT HOLDER(S) BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
 * OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * ---------------------------------------------------------------------------*/

#include "PosixSource.h"
#include "Rts.h"

#include "RtsUtils.h"
#include "RBTree.h"

STATIC_INLINE StgRB*
rbRotateLeft(Capability *cap, StgRB *a) {
    ASSERT(a != RB_NULL);
    StgRB *r = RB_RIGHT_GET(a);
    ASSERT(r != RB_NULL);
    RB_RIGHT_SET(cap, a, RB_LEFT_GET(r));
    RB_LEFT_SET(cap, r, a);
    return r;
}

STATIC_INLINE StgRB*
rbRotateRight(Capability *cap, StgRB *a) {
    ASSERT(a != RB_NULL);
    StgRB *l = RB_LEFT_GET(a);
    ASSERT(l != RB_NULL);
    RB_LEFT_SET(cap, a, RB_RIGHT_GET(l));
    RB_RIGHT_SET(cap, l, a);
    return l;
}

int
checkRBTree(StgRB *r, int forceBlack, int count, int expected)
{
    if (r == RB_NULL) {
        ASSERT(expected == -1 || count == expected);
        ASSERT(count != 0);
        return count;
    }
    ASSERT(LOOKS_LIKE_CLOSURE_PTR(RB_LEFT_GET(r)));
    ASSERT(LOOKS_LIKE_CLOSURE_PTR(RB_RIGHT_GET(r)));
    ASSERT(LOOKS_LIKE_CLOSURE_PTR(RB_HEAD_GET(r)));
    ASSERT(LOOKS_LIKE_CLOSURE_PTR(RB_TAIL_GET(r)));
    if (count == 0) {
        // this corresponds to "fast path" empty node
        if (RB_HEAD_GET(r) == END_TSO_QUEUE) {
            ASSERT(RB_LEFT_GET(r) == RB_NULL);
            ASSERT(RB_RIGHT_GET(r) == RB_NULL);
            ASSERT(RB_TAIL_GET(r) == END_TSO_QUEUE);
            ASSERT(RB_IS_BLACK(r));
        }
        return 0;
    } else {
        ASSERT(RB_HEAD_GET(r) != END_TSO_QUEUE);
        ASSERT(RB_TAIL_GET(r) != END_TSO_QUEUE);
    }
    ASSERT(LOOKS_LIKE_CLOSURE_PTR(RB_COLOR_GET(r)));
    ASSERT(RB_COLOR_GET(r) == RB_RED || RB_COLOR_GET(r) == RB_BLACK);
    if (forceBlack) {
        ASSERT(RB_IS_BLACK(r));
    }
    if (RB_IS_BLACK(r)) {
        count++;
    }
    expected = checkRBTree(RB_LEFT_GET(r), RB_IS_RED(r), count, expected);
    checkRBTree(RB_RIGHT_GET(r), RB_IS_RED(r), count, expected);
    return expected;
}

void
rbEvacuate(evac_fn evac, void *user, StgRB* r) {
    if (r == RB_NULL) return;
    evac(user, (StgClosure **)(void *)&r->head);
    evac(user, (StgClosure **)(void *)&r->tail);
    rbEvacuate(evac, user, r->left);
    rbEvacuate(evac, user, r->right); // XXX maybe manually TCO this
}

// this function assumes you've checked for fastpath
StgRB*
rbInsert(Capability *cap, StgRB **root, StgTSO *tso) {
    struct {
        StgRB *node;
        int cmp;
    } path[sizeof(void *) << 4], *pathp;
    path->node = *root;
    int found = 0;
    // Wind
    for (pathp = path; pathp->node != RB_NULL; pathp++) {
        ASSERT(RB_HEAD_GET(pathp->node) != END_TSO_QUEUE); // e.g. root is NOT a fast path empty node
        ASSERT(RB_TAIL_GET(pathp->node) != END_TSO_QUEUE);
        StgWord64 pass = RB_HEAD_GET(pathp->node)->ss_pass;
        int cmp = pathp->cmp = (tso->ss_pass > pass) - (tso->ss_pass < pass);
        if (cmp < 0) {
            pathp[1].node = RB_LEFT_GET(pathp->node);
        } else if (cmp == 0) {
            found = 1;
            break;
        } else {
            pathp[1].node = RB_RIGHT_GET(pathp->node);
        }
    }
    if (found) { // O(n log n) pointer traverals but only O(1) edits
        ASSERT(pathp->node != RB_NULL);
        ASSERT(RB_HEAD_GET(pathp->node) != END_TSO_QUEUE);
        setTSOLink(cap, RB_TAIL_GET(pathp->node), tso);
        RB_TAIL_SET(cap, pathp->node, tso);
        return pathp->node;
    }
    StgRB *node = rbCreateNode(cap, tso);
    pathp->node = node;
    // Unwind
    for (pathp--; (void*)pathp >= (void*)path; pathp--) {
        StgRB *cnode = pathp->node;
        ASSERT(cnode != RB_NULL);
        ASSERT(pathp->cmp != 0);
        if (pathp->cmp < 0) {
            StgRB *left = pathp[1].node;
            RB_LEFT_SET(cap, cnode, left);
            if (RB_IS_RED(left)) {
                StgRB *leftleft = RB_LEFT_GET(left);
                if (RB_IS_RED(leftleft)) {
                    // fix up 4-node
                    StgRB *tnode;
                    RB_COLOR_BLACK(cap, leftleft);
                    tnode = rbRotateRight(cap, cnode);
                    cnode = tnode;
                }
            } else {
                return node;
            }
        } else {
            StgRB *right = pathp[1].node;
            RB_RIGHT_SET(cap, cnode, right);
            if (RB_IS_RED(right)) {
                StgRB *left = RB_LEFT_GET(cnode);
                if (RB_IS_RED(left)) {
                    // split 4-node
                    RB_COLOR_BLACK(cap, left);
                    RB_COLOR_BLACK(cap, right);
                    RB_COLOR_RED(cap, cnode);
                } else {
                    // lean left
                    StgRB *tnode;
                    StgClosure *tred = RB_COLOR_GET(cnode);
                    tnode = rbRotateLeft(cap, cnode);
                    RB_COLOR_SET(cap, tnode, tred);
                    RB_COLOR_RED(cap, cnode);
                    cnode = tnode;
                }
            } else {
                return node;
            }
        }
        pathp->node = cnode;
    }
    *root = path->node;
    RB_COLOR_BLACK(cap, *root);
    return node;
}

// this function assumes you've checked for fastpath
StgTSO*
rbRemoveMin(Capability *cap, StgRB **root) {
    struct {
        StgRB *node;
        int cmp;
    } path[sizeof(void *) << 4], *pathp, *nodep;
    // Wind
    nodep = NULL;
    path->node = *root;
    for (pathp = path; pathp->node != RB_NULL; pathp++) {
        ASSERT(RB_HEAD_GET(pathp->node) != END_TSO_QUEUE); // e.g. fast path is NOT in effect
        ASSERT(RB_TAIL_GET(pathp->node) != END_TSO_QUEUE);
        StgRB *left = RB_LEFT_GET(pathp->node);
        if (left != RB_NULL) {
            pathp->cmp = -1;
            pathp[1].node = left;
        } else {
            // Find node's successor, in preparation for swap
            // XXX defer this for later
            pathp[1].node = RB_RIGHT_GET(pathp->node);
            pathp->cmp = 1;
            nodep = pathp;
            for (pathp++; pathp->node != RB_NULL; pathp++) {
                pathp->cmp = -1;
                pathp[1].node = RB_LEFT_GET(pathp->node);
            }
            break;
        }
    }
    ASSERT(nodep->node != RB_NULL);
    StgTSO *tso = RB_HEAD_GET(nodep->node);
    if (tso->_link != END_TSO_QUEUE) { // fast-path!
        RB_HEAD_SET(cap, nodep->node, tso->_link);
        tso->_link = END_TSO_QUEUE;
        return tso; // not to cleanup: no free node!
    }
    tso->_link = END_TSO_QUEUE;
    pathp--;
    StgRB *node = nodep->node; // the node to be deleted
    if (pathp->node != node) {
        ASSERT(pathp->node != RB_NULL);
        // swap node with its successor
        StgClosure *tred = RB_COLOR_GET(pathp->node);
        RB_COLOR_SET(cap, pathp->node, RB_COLOR_GET(node));
        ASSERT(RB_HEAD_GET(pathp->node) != END_TSO_QUEUE); // e.g. fast path is NOT in effect
        ASSERT(RB_TAIL_GET(pathp->node) != END_TSO_QUEUE);
        RB_LEFT_SET(cap, pathp->node, RB_LEFT_GET(node));
        // if node's successor is its right child, the following code
        // will do the wrong thing for the right child pointer.
        // However, it doesn't matter, because the pointer will be
        // properly set when the successor is pruned.
        RB_RIGHT_SET(cap, pathp->node, RB_RIGHT_GET(node));
        RB_COLOR_SET(cap, node, tred);
        // the pruned leaf node's child pointers are never accessed
        // again, so don't bother setting them to nil
        nodep->node = pathp->node;
        pathp->node = node;
        if (nodep == path) {
            *root = nodep->node;
        } else {
            if (nodep[-1].cmp < 0) {
                RB_LEFT_SET(cap, nodep[-1].node, nodep->node);
            } else {
                RB_RIGHT_SET(cap, nodep[-1].node, nodep->node);
            }
        }
    } else {
        StgRB *left = RB_LEFT_GET(node);
        if (left != RB_NULL) {
            // node has no successor, but it has a left child.
            // splice node out, without losing the left child
            ASSERT(RB_IS_BLACK(node));
            ASSERT(RB_IS_RED(left));
            RB_COLOR_BLACK(cap, left);
            if (pathp == path) {
                *root = left;
            } else {
                if (pathp[-1].cmp < 0) {
                    RB_LEFT_SET(cap, pathp[-1].node, left);
                } else {
                    RB_RIGHT_SET(cap, pathp[-1].node, left);
                }
            }
            goto cleanup;
        } else if (pathp == path) {
            // the tree contained only one node
            // *root = RB_NULL;
            // instead, setup fastpath
            RB_HEAD_SET(cap, *root, END_TSO_QUEUE);
            RB_TAIL_SET(cap, *root, END_TSO_QUEUE);
            ASSERT(RB_LEFT_GET(*root) == RB_NULL);
            ASSERT(RB_RIGHT_GET(*root) == RB_NULL);
            // do NOT add to free list
            return tso;
        }
    }
    if (RB_IS_RED(pathp->node)) {
        // prune red node, which requires no fixup
        ASSERT(pathp[-1].cmp < 0);
        RB_LEFT_SET(cap, pathp[-1].node, RB_NULL);
        goto cleanup;
    }
    // the node to be pruned is black, so unwind until balance
    // is restored
    pathp->node = RB_NULL;
    for (pathp--; (void*)pathp >= (void*)path; pathp--) {
        ASSERT(pathp->node != RB_NULL);
        ASSERT(pathp->cmp != 0);
        if (pathp->cmp < 0) {
            RB_LEFT_SET(cap, pathp->node, pathp[1].node);
            ASSERT(RB_IS_BLACK(pathp[1].node));
            if (RB_IS_RED(pathp->node)) {
                StgRB *right = RB_RIGHT_GET(pathp->node);
                ASSERT(right != RB_NULL);
                StgRB *rightleft = RB_LEFT_GET(right);
                StgRB *tnode;
                if (RB_IS_RED(rightleft)) {
                    /* In the following diagrams, ||, //, and \\      */
                    /* indicate the path to the removed node.         */
                    /*                                                */
                    /*      ||                                        */
                    /*    pathp(r)                                    */
                    /*  //        \                                   */
                    /* (b)        (b)                                 */
                    /*           /                                    */
                    /*          (r)                                   */
                    /*                                                */
                    RB_COLOR_BLACK(cap, pathp->node);
                    tnode = rbRotateRight(cap, right);
                    RB_RIGHT_SET(cap, pathp->node, tnode);
                    tnode = rbRotateLeft(cap, pathp->node);
                } else {
                    /*      ||                                        */
                    /*    pathp(r)                                    */
                    /*  //        \                                   */
                    /* (b)        (b)                                 */
                    /*           /                                    */
                    /*          (b)                                   */
                    /*                                                */
                    tnode = rbRotateLeft(cap, pathp->node);
                }
                // balance restored, but rotation modified subtree root.
                ASSERT(pathp > path);
                if (pathp[-1].cmp < 0) {
                    RB_LEFT_SET(cap, pathp[-1].node, tnode);
                } else {
                    RB_RIGHT_SET(cap, pathp[-1].node, tnode);
                }
                goto cleanup;
            } else {
                StgRB *right = RB_RIGHT_GET(pathp->node);
                ASSERT(right != RB_NULL);
                StgRB *rightleft = RB_LEFT_GET(right);
                if (RB_IS_RED(rightleft)) {
                    /*      ||                                        */
                    /*    pathp(b)                                    */
                    /*  //        \                                   */
                    /* (b)        (b)                                 */
                    /*           /                                    */
                    /*          (r)                                   */
                    StgRB *tnode;
                    RB_COLOR_BLACK(cap, rightleft);
                    tnode = rbRotateRight(cap, right);
                    RB_RIGHT_SET(cap, pathp->node, tnode);
                    tnode = rbRotateLeft(cap, pathp->node);
                    // balance restored, but rotation modified
                    // subtree root, which may actually be the tree root
                    if (pathp == path) {
                        // set root
                        *root = tnode;
                    } else {
                        if (pathp[-1].cmp < 0) {
                            RB_LEFT_SET(cap, pathp[-1].node, tnode);
                        } else {
                            RB_RIGHT_SET(cap, pathp[-1].node, tnode);
                        }
                    }
                    goto cleanup;
                } else {
                    /*      ||                                        */
                    /*    pathp(b)                                    */
                    /*  //        \                                   */
                    /* (b)        (b)                                 */
                    /*           /                                    */
                    /*          (b)                                   */
                    StgRB *tnode;
                    RB_COLOR_RED(cap, pathp->node);
                    tnode = rbRotateLeft(cap, pathp->node);
                    pathp->node = tnode;
                }
            }
        } else {
            StgRB *left;
            RB_RIGHT_SET(cap, pathp->node, pathp[1].node);
            left = RB_LEFT_GET(pathp->node);
            ASSERT(left != RB_NULL);
            if (RB_IS_RED(left)) {
                StgRB *tnode;
                StgRB *leftright = RB_RIGHT_GET(left);
                ASSERT(leftright != RB_NULL);
                StgRB *leftrightleft = RB_LEFT_GET(leftright);
                if (RB_IS_RED(leftrightleft)) {
                    /*      ||                                        */
                    /*    pathp(b)                                    */
                    /*   /        \\                                  */
                    /* (r)        (b)                                 */
                    /*   \                                            */
                    /*   (b)                                          */
                    /*   /                                            */
                    /* (r)                                            */
                    StgRB *unode;
                    RB_COLOR_BLACK(cap, leftrightleft);
                    unode = rbRotateRight(cap, pathp->node);
                    tnode = rbRotateRight(cap, pathp->node);
                    RB_RIGHT_SET(cap, unode, tnode);
                    tnode = rbRotateLeft(cap, unode);
                } else {
                    /*      ||                                        */
                    /*    pathp(b)                                    */
                    /*   /        \\                                  */
                    /* (r)        (b)                                 */
                    /*   \                                            */
                    /*   (b)                                          */
                    /*   /                                            */
                    /* (b)                                            */
                    ASSERT(leftright != RB_NULL);
                    RB_COLOR_RED(cap, leftright);
                    tnode = rbRotateRight(cap, pathp->node);
                    RB_COLOR_BLACK(cap, tnode);
                }
                /* Balance restored, but rotation modified subtree    */
                /* root, which may actually be the tree root.         */
                if (pathp == path) {
                    /* Set root. */
                    *root = tnode;
                } else {
                    if (pathp[-1].cmp < 0) {
                        RB_LEFT_SET(cap, pathp[-1].node, tnode);
                    } else {
                        RB_RIGHT_SET(cap, pathp[-1].node, tnode);
                    }
                }
                goto cleanup;
            } else if (RB_IS_RED(pathp->node)) {
                StgRB *leftleft = RB_LEFT_GET(left);
                if (RB_IS_RED(leftleft)) {
                    /*        ||                                      */
                    /*      pathp(r)                                  */
                    /*     /        \\                                */
                    /*   (b)        (b)                               */
                    /*   /                                            */
                    /* (r)                                            */
                    StgRB *tnode;
                    RB_COLOR_BLACK(cap, pathp->node);
                    RB_COLOR_RED(cap, left);
                    RB_COLOR_BLACK(cap, leftleft);
                    tnode = rbRotateRight(cap, pathp->node);
                    /* Balance restored, but rotation modified        */
                    /* subtree root.                                  */
                    ASSERT(pathp > path);
                    if (pathp[-1].cmp < 0) {
                        RB_LEFT_SET(cap, pathp[-1].node, tnode);
                    } else {
                        RB_RIGHT_SET(cap, pathp[-1].node, tnode);
                    }
                    goto cleanup;
                } else {
                    /*        ||                                      */
                    /*      pathp(r)                                  */
                    /*     /        \\                                */
                    /*   (b)        (b)                               */
                    /*   /                                            */
                    /* (b)                                            */
                    RB_COLOR_RED(cap, left);
                    RB_COLOR_BLACK(cap, pathp->node);
                    /* Balance restored. */
                    goto cleanup;
                }
            } else {
                StgRB *leftleft = RB_LEFT_GET(left);
                if (RB_IS_RED(leftleft)) {
                    /*               ||                               */
                    /*             pathp(b)                           */
                    /*            /        \\                         */
                    /*          (b)        (b)                        */
                    /*          /                                     */
                    /*        (r)                                     */
                    StgRB *tnode;
                    RB_COLOR_BLACK(cap, leftleft);
                    tnode = rbRotateRight(cap, pathp->node);
                    /* Balance restored, but rotation modified        */
                    /* subtree root, which may actually be the tree   */
                    /* root.                                          */
                    if (pathp == path) {
                        /* Set root. */
                        *root = tnode;
                    } else {
                        if (pathp[-1].cmp < 0) {
                            RB_LEFT_SET(cap, pathp[-1].node, tnode);
                        } else {
                            RB_RIGHT_SET(cap, pathp[-1].node, tnode);
                        }
                    }
                    goto cleanup;
                } else {
                    /*               ||                               */
                    /*             pathp(b)                           */
                    /*            /        \\                         */
                    /*          (b)        (b)                        */
                    /*          /                                     */
                    /*        (b)                                     */
                    RB_COLOR_RED(cap, left);
                }
            }
        }
    }
    // set root
    *root = path->node;
    ASSERT(RB_IS_BLACK(*root));
cleanup:
    // return node to the free list
    RB_LEFT_SET(cap, node, cap->rb_free_list);
#ifdef DEBUG
    RB_RIGHT_SET(cap, node, RB_NULL);
    RB_HEAD_SET(cap, node, END_TSO_QUEUE);
    RB_TAIL_SET(cap, node, END_TSO_QUEUE);
#endif
    cap->rb_free_list = node;
    return tso;
}
