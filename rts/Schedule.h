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

/* END_TSO_QUEUE and friends now defined in includes/StgMiscClosures.h */

/* Add a thread to the end of the run queue.
 * NOTE: tso->link should be END_TSO_QUEUE before calling this macro.
 * ASSUMES: cap->running_task is the current task.
 */
EXTERN_INLINE void
appendToRunQueue (Capability *cap, StgTSO *tso);

EXTERN_INLINE void
appendToRunQueue (Capability *cap, StgTSO *tso)
{
    ASSERT(tso->_link == END_TSO_QUEUE);
    tso->ss_pass += tso->ss_stride;
    if (cap->run_queue_hd == END_TSO_QUEUE) {
	cap->run_queue_hd = tso;
        tso->block_info.prev = END_TSO_QUEUE;
        cap->run_queue_tl = tso;
    } else {
        StgTSO *t, *next;
        next = END_TSO_QUEUE;
        for (t = cap->run_queue_tl; t != END_TSO_QUEUE; next = t, t = t->block_info.prev) {
            if (tso->ss_pass >= t->ss_pass || t->flags & TSO_PROMOTED) {
                if (next == END_TSO_QUEUE) {
                    // it's the last one!
                    // this should overwhelmingly be the case when priorities
                    // are not being set
                    setTSOLink(cap, cap->run_queue_tl, tso);
                    setTSOPrev(cap, tso, cap->run_queue_tl);
                    cap->run_queue_tl = tso;
                } else {
                    // XXX is there like a necessary order or something?
                    setTSOLink(cap, tso, next);
                    setTSOPrev(cap, tso, t);
                    setTSOLink(cap, t, tso);
                    setTSOPrev(cap, next, tso);
                }
                break;
            }
        }
        if (t == END_TSO_QUEUE) {
            setTSOLink(cap, tso, cap->run_queue_hd);
            tso->block_info.prev = END_TSO_QUEUE;
            cap->run_queue_hd = tso;
        }
    }
}

INLINE_HEADER void
joinRunQueue(Capability *cap, StgTSO *tso) {
    tso->ss_pass = cap->ss_pass + tso->ss_remain;
    tso->flags &= ~TSO_PROMOTED;
    appendToRunQueue(cap, tso);
}

/* Push a thread on the beginning of the run queue.
 * ASSUMES: cap->running_task is the current task.
 */
EXTERN_INLINE void
pushOnRunQueue (Capability *cap, StgTSO *tso);

// This code is a little dangerous, since it temporarily bypasses
// stride scheduling.  However, since we do increase ss_pass,
// as long as the process doesn't continually get rescheduled with
// pushOn, it will eventually be penalized for the time it took.
// Since I think the old code was written to avoid this kid of
// starvation, deferred punishment should be OK. (Also, failing
// to put threads in front after they allocate causes massive
// performance problems.)
EXTERN_INLINE void
pushOnRunQueue (Capability *cap, StgTSO *tso)
{
    tso->ss_pass += tso->ss_stride;
    tso->flags |= TSO_PROMOTED;
    setTSOLink(cap, tso, cap->run_queue_hd);
    tso->block_info.prev = END_TSO_QUEUE;
    if (cap->run_queue_hd != END_TSO_QUEUE) {
        setTSOPrev(cap, cap->run_queue_hd, tso);
    }
    cap->run_queue_hd = tso;
    if (cap->run_queue_tl == END_TSO_QUEUE) {
        cap->run_queue_tl = tso;
    }
}

INLINE_HEADER void
fastJoinRunQueue(Capability *cap, StgTSO *tso) {
    tso->ss_pass = cap->ss_pass + tso->ss_remain;
    pushOnRunQueue(cap, tso);
}

/* Pop the first thread off the runnable queue.
 */
INLINE_HEADER StgTSO *
popRunQueue (Capability *cap)
{ 
    StgTSO *t = cap->run_queue_hd;
    ASSERT(t != END_TSO_QUEUE);
    cap->run_queue_hd = t->_link;
    if (t->_link != END_TSO_QUEUE) {
        t->_link->block_info.prev = END_TSO_QUEUE;
    }
    t->_link = END_TSO_QUEUE; // no write barrier req'd
    if (cap->run_queue_hd == END_TSO_QUEUE) {
	cap->run_queue_tl = END_TSO_QUEUE;
    }
    if (t->flags & TSO_PROMOTED) {
        t->flags &= ~TSO_PROMOTED;
        // its pass is nonsense, don't count it
    } else {
        if (cap->run_queue_hd != END_TSO_QUEUE) {
            // relies on a PROMOTED invariant: promoted elements
            // are ALWAYS in the front of the queue
            ASSERT(cap->run_queue_hd->flags & TSO_PROMOTED == 0);
            cap->ss_pass = cap->run_queue_hd->ss_pass;
        }
    }
    return t;
}

INLINE_HEADER StgTSO *
peekRunQueue (Capability *cap)
{
    return cap->run_queue_hd;
}

INLINE_HEADER void
leaveRunQueue (Capability *cap STG_UNUSED, StgTSO *tso STG_UNUSED)
{
    int r = tso->ss_pass - cap->ss_pass;
    if (r > 0) {
        tso->ss_remain = (StgWord32)r;
    } else {
        tso->ss_remain = 0;
    }
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
    return emptyQueue(cap->run_queue_hd);
}

/* assumes that the queue is not empty; so combine this with
 * an emptyRunQueue check! */
INLINE_HEADER rtsBool
singletonRunQueue(Capability *cap)
{
    ASSERT(!emptyRunQueue(cap));
    return cap->run_queue_hd->_link == END_TSO_QUEUE;
}

INLINE_HEADER void
truncateRunQueue(Capability *cap)
{
    cap->run_queue_hd = END_TSO_QUEUE;
    cap->run_queue_tl = END_TSO_QUEUE;
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

