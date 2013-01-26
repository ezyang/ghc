/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team 1998-2005
 *
 * Prototypes for functions in Schedule.c 
 * (RTS internal scheduler interface)
 *
 * -------------------------------------------------------------------------*/

#ifndef SCHEDULE_H
#define SCHEDULE_H

#include "rts/OSThreads.h"
#include "Capability.h"
#include "Trace.h"
#include "RBTree.h"

#include "BeginPrivate.h"

/* initScheduler(), exitScheduler()
 * Called from STG :  no
 * Locks assumed   :  none
 */
void initScheduler (void);
void exitScheduler (rtsBool wait_foreign);
void freeScheduler (void);
void markScheduler (evac_fn evac, void *user);

// Place a new thread on the run queue of the current Capability
void scheduleThread (Capability *cap, StgTSO *tso);

// Place a new thread on the run queue of a specified Capability
// (cap is the currently owned Capability, cpu is the number of
// the desired Capability).
void scheduleThreadOn(Capability *cap, StgWord cpu, StgTSO *tso);

/* wakeUpRts()
 * 
 * Causes an OS thread to wake up and run the scheduler, if necessary.
 */
#if defined(THREADED_RTS)
void wakeUpRts(void);
#endif

/* raiseExceptionHelper */
StgWord raiseExceptionHelper (StgRegTable *reg, StgTSO *tso, StgClosure *exception);

/* findRetryFrameHelper */
StgWord findRetryFrameHelper (Capability *cap, StgTSO *tso);

/* Entry point for a new worker */
void scheduleWorker (Capability *cap, Task *task);

/* The state of the scheduler.  This is used to control the sequence
 * of events during shutdown, and when the runtime is interrupted
 * using ^C.
 */
#define SCHED_RUNNING       0  /* running as normal */
#define SCHED_INTERRUPTING  1  /* ^C detected, before threads are deleted */
#define SCHED_SHUTTING_DOWN 2  /* final shutdown */

extern volatile StgWord sched_state;

/* 
 * flag that tracks whether we have done any execution in this time
 * slice, and controls the disabling of the interval timer.
 *
 * The timer interrupt transitions ACTIVITY_YES into
 * ACTIVITY_MAYBE_NO, waits for RtsFlags.GcFlags.idleGCDelayTime,
 * and then:
 *   - if idle GC is no, set ACTIVITY_INACTIVE and wakeUpRts()
 *   - if idle GC is off, set ACTIVITY_DONE_GC and stopTimer()
 *
 * If the scheduler finds ACTIVITY_INACTIVE, then it sets
 * ACTIVITY_DONE_GC, performs the GC and calls stopTimer().
 *
 * If the scheduler finds ACTIVITY_DONE_GC and it has a thread to run,
 * it enables the timer again with startTimer().
 */
#define ACTIVITY_YES      0
  // the RTS is active
#define ACTIVITY_MAYBE_NO 1
  // no activity since the last timer signal
#define ACTIVITY_INACTIVE 2
  // RtsFlags.GcFlags.idleGCDelayTime has passed with no activity
#define ACTIVITY_DONE_GC  3
  // like ACTIVITY_INACTIVE, but we've done a GC too (if idle GC is
  // enabled) and the interval timer is now turned off.

/* Recent activity flag.
 * Locks required  : Transition from MAYBE_NO to INACTIVE
 * happens in the timer signal, so it is atomic.  Trnasition from
 * INACTIVE to DONE_GC happens under sched_mutex.  No lock required
 * to set it to ACTIVITY_YES.
 */
extern volatile StgWord recent_activity;

/* Thread queues.
 * Locks required  : sched_mutex
 *
 * In GranSim we have one run/blocked_queue per PE.
 */
extern  StgTSO *blackhole_queue;
#if !defined(THREADED_RTS)
extern  StgTSO *blocked_queue_hd, *blocked_queue_tl;
extern  StgTSO *sleeping_queue;
#endif

extern rtsBool heap_overflow;

#if defined(THREADED_RTS)
extern Mutex sched_mutex;
#endif

/* Called by shutdown_handler(). */
void interruptStgRts (void);

void resurrectThreads (StgTSO *);

// STRIDE1 defines the maximum resolution we can achieve in scheduling.
#define STRIDE1 (1 << 20)
// Defualt tickets is set to STRIDE1, so that the IO manager gets
// maximum priority.
#define DEFAULT_TICKETS (1 << 20)

/* -----------------------------------------------------------------------------
 * Some convenient macros/inline functions...
 */

#if !IN_STG_CODE

/* END_TSO_QUEUE and friends now defined in includes/stg/MiscClosures.h */

/* Add a thread to the end of the run queue.
 * NOTE: tso->link should be END_TSO_QUEUE before calling this macro.
 * ASSUMES: cap->running_task is the current task.
 */
EXTERN_INLINE void
appendToRunQueue (Capability *cap, StgTSO *tso);

EXTERN_INLINE void
appendToRunQueue (Capability *cap, StgTSO *tso)
{
    tso->block_info.closure = (StgClosure*)END_TSO_QUEUE;
    tso->ss_pass += STRIDE1 / tso->ss_tickets;
    StgTSO *cur = RB_HEAD_GET(cap->run_active);
    cap->run_count++;
    if (cur == END_TSO_QUEUE) {
        // fastpath
        ASSERT(RB_IS_BLACK(cap->run_active));
        ASSERT(RB_LEFT_GET(cap->run_active) == RB_NULL);
        ASSERT(RB_RIGHT_GET(cap->run_active) == RB_NULL);
        RB_HEAD_SET(cap, cap->run_active, tso);
        RB_TAIL_SET(cap, cap->run_active, tso);
    } else {
        StgWord64 pass = cur->ss_pass;
        if (tso->ss_pass < pass) {
            cap->run_active = rbInsert(cap, &cap->run_rbtree, tso);
        } else if (tso->ss_pass == pass) {
            setTSOLink(cap, RB_TAIL_GET(cap->run_active), tso);
            RB_TAIL_SET(cap, cap->run_active, tso);
        } else {
            rbInsert(cap, &cap->run_rbtree, tso);
        }
        IF_DEBUG(sanity, checkRBTree(cap->run_rbtree, 1, 0, -1));
    }
}

EXTERN_INLINE void
joinRunQueue(Capability *cap, StgTSO *tso);

EXTERN_INLINE void
joinRunQueue(Capability *cap, StgTSO *tso)
{
    tso->ss_pass = cap->ss_pass - STRIDE1 / tso->ss_tickets;
    appendToRunQueue(cap, tso);
}

/* Push a thread on the beginning of the run queue.
 * ASSUMES: cap->running_task is the current task.
 */
EXTERN_INLINE void
pushOnRunQueue (Capability *cap, StgTSO *tso);

EXTERN_INLINE void
pushOnRunQueue (Capability *cap, StgTSO *tso)
{
    tso->block_info.closure = (StgClosure*)END_TSO_QUEUE;
    tso->ss_pass += STRIDE1 / tso->ss_tickets;
    cap->run_count++;
    if (cap->promoted_run_queue_hd == END_TSO_QUEUE) {
    } else {
        setTSOLink(cap, tso, cap->promoted_run_queue_hd);
    }
    cap->promoted_run_queue_hd = tso;
}

EXTERN_INLINE void
fastJoinRunQueue(Capability *cap, StgTSO *tso);

EXTERN_INLINE void
fastJoinRunQueue(Capability *cap, StgTSO *tso)
{
    tso->ss_pass = cap->ss_pass - STRIDE1 / tso->ss_tickets;
    pushOnRunQueue(cap, tso);
}

/* Pop the first thread off the runnable queue.
 */
INLINE_HEADER StgTSO *
popRunQueue (Capability *cap)
{ 
    cap->run_count--;
    if (cap->promoted_run_queue_hd == END_TSO_QUEUE) {
        StgTSO *candidate = RB_HEAD_GET(cap->run_active);
        if (candidate == END_TSO_QUEUE) {
            barf("popRunQueue: queue is empty");
        }
        if ( // unconditional fastpath (no-rb tree)
             (candidate->_link != END_TSO_QUEUE) ||
             // fastpath for a queue that just got emptied
             (cap->run_rbtree == cap->run_active && RB_RIGHT_GET(cap->run_active) == RB_NULL)
        ) {
            RB_HEAD_SET(cap, cap->run_active, candidate->_link);
            if (candidate->_link == END_TSO_QUEUE) {
                RB_TAIL_SET(cap, cap->run_active, END_TSO_QUEUE);
            }
            candidate->_link = END_TSO_QUEUE;
            return candidate;
        }
        StgTSO *t = rbRemoveMin(cap, &cap->run_rbtree);
        IF_DEBUG(sanity, checkRBTree(cap->run_rbtree, 1, 0, -1));
        // XXX maybe this can be folded into removeMin
        cap->run_active = rbFirst(cap->run_rbtree);
        if (RB_HEAD_GET(cap->run_active) != END_TSO_QUEUE) {
            StgWord64 npass = RB_HEAD_GET(cap->run_active)->ss_pass;
            if (npass > cap->ss_pass) {
                cap->ss_pass = npass;
            }
        }
        return t;
    } else {
        StgTSO *t = cap->promoted_run_queue_hd;
        cap->promoted_run_queue_hd = t->_link;
        t->_link = END_TSO_QUEUE; // no write barrier req'd
        return t;
    }
}

INLINE_HEADER StgTSO *
peekRunQueue (Capability *cap)
{
    if (cap->promoted_run_queue_hd == END_TSO_QUEUE) {
        return RB_HEAD_GET(cap->run_active);
    } else {
        return cap->promoted_run_queue_hd;
    }
}

EXTERN_INLINE void
leaveRunQueue (Capability *cap, StgTSO *tso);

EXTERN_INLINE void
leaveRunQueue (Capability *cap STG_UNUSED, StgTSO *tso STG_UNUSED)
{
    // XXX implement me
}

void removeFromRunQueue (Capability *cap, StgTSO *tso);
extern void promoteInRunQueue (Capability *cap, StgTSO *tso);

/* Add a thread to the end of the blocked queue.
 */
#if !defined(THREADED_RTS)
INLINE_HEADER void
appendToBlockedQueue(StgTSO *tso)
{
    ASSERT(tso->_link == END_TSO_QUEUE);
    if (blocked_queue_hd == END_TSO_QUEUE) {
       blocked_queue_hd = tso;
    } else {
       setTSOLink(&MainCapability, blocked_queue_tl, tso);
    }
    blocked_queue_tl = tso;
}
#endif

/* Check whether various thread queues are empty
 */
INLINE_HEADER rtsBool
emptyQueue (StgTSO *q)
{
    return (q == END_TSO_QUEUE);
}

INLINE_HEADER rtsBool
emptyRunQueue(Capability *cap)
{
    return cap->run_count == 0;
}

INLINE_HEADER rtsBool
singletonRunQueue(Capability *cap)
{
    return cap->run_count == 1;
}

INLINE_HEADER void
truncateRunQueue(Capability *cap)
{
    cap->promoted_run_queue_hd = END_TSO_QUEUE;
    // XXX leak
    cap->run_rbtree = cap->run_active = rbCreateNode(cap, END_TSO_QUEUE);
    cap->run_count = 0;
}

#if !defined(THREADED_RTS)
#define EMPTY_BLOCKED_QUEUE()  (emptyQueue(blocked_queue_hd))
#define EMPTY_SLEEPING_QUEUE() (emptyQueue(sleeping_queue))
#endif

INLINE_HEADER rtsBool
emptyThreadQueues(Capability *cap)
{
    return emptyRunQueue(cap)
#if !defined(THREADED_RTS)
	&& EMPTY_BLOCKED_QUEUE() && EMPTY_SLEEPING_QUEUE()
#endif
    ;
}

#endif /* !IN_STG_CODE */

#include "EndPrivate.h"

#endif /* SCHEDULE_H */

