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

/* END_TSO_QUEUE and friends now defined in includes/stg/MiscClosures.h */
EXTERN_INLINE void
annulTSO(StgTSO *tso);

EXTERN_INLINE void
annulTSO(StgTSO *tso) {
    // hack to make some invariants with regards to block_info and _link work
    // this is called whereever we would have stepped all over the
    // fields in the linked list implementation
    ASSERT(tso->_link == END_TSO_QUEUE);
    tso->block_info.closure = (StgClosure*)END_TSO_QUEUE;
}

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
    tso->ss_pass = cap->ss_pass++;                                          // [EMU]
    //tso->ss_pass += STRIDE1 / tso->ss_tickets;                            // [EMU]
    annulTSO(tso);
    insertPQueue(cap->run_pqueue, tso);
}

EXTERN_INLINE void
joinRunQueue(Capability *cap, StgTSO *tso);

EXTERN_INLINE void
joinRunQueue(Capability *cap, StgTSO *tso)
{
    tso->ss_pass = cap->ss_pass++;
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
    annulTSO(tso);                                                          // [EMU]
    //tso->ss_pass += STRIDE1 / tso->ss_tickets;                            // [EMU]
    if (cap->promoted_run_queue_hd == END_TSO_QUEUE) {
        // annulTSO invariant used here
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
    tso->ss_pass = cap->ss_pass++;                                          // [EMU]
    pushOnRunQueue(cap, tso);
}

/* Pop the first thread off the runnable queue.
 */
INLINE_HEADER StgTSO *
popRunQueue (Capability *cap)
{
    if (cap->promoted_run_queue_hd == END_TSO_QUEUE) {
        StgTSO *t = deleteMinPQueue(cap->run_pqueue);
        StgTSO *next = peekMinPQueue(cap->run_pqueue);
        /* if (next != NULL) {
            if (cap->ss_pass < next->ss_pass) {
                cap->ss_pass = next->ss_pass;
            }
        } */                                                                // [EMU]
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
        return peekMinPQueue(cap->run_pqueue);
    } else {
        return cap->promoted_run_queue_hd;
    }
}

EXTERN_INLINE void
leaveRunQueue(Capability *cap, StgTSO *tso);

EXTERN_INLINE void
leaveRunQueue(Capability *cap, StgTSO *tso)
{
    // XXX implement me
}

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
    return cap->promoted_run_queue_hd == END_TSO_QUEUE && peekMinPQueue(cap->run_pqueue) == NULL;
}

/* assumes that the queue is not empty; so combine this with
 * an emptyRunQueue check! */
INLINE_HEADER rtsBool
singletonRunQueue(Capability *cap)
{
    if (cap->promoted_run_queue_hd != END_TSO_QUEUE) {
        if (cap->run_pqueue->size != 0) return 0;
        return cap->promoted_run_queue_hd->_link == END_TSO_QUEUE;
    } else {
        return cap->run_pqueue->size == 1;
    }
}

INLINE_HEADER void
truncateRunQueue(Capability *cap)
{
    cap->promoted_run_queue_hd = END_TSO_QUEUE;
    truncatePQueue(cap->run_pqueue);
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

