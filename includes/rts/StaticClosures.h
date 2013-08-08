/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2009
 *
 * _closure macros for static closures, which will properly handle
 * indirection.
 *
 * NB: THIS FILE IS INCLUDED IN NON-C CODE AND DATA!  #defines only please.
 *
 * To understand the structure of the RTS headers, see the wiki:
 *   http://hackage.haskell.org/trac/ghc/wiki/Commentary/SourceTree/Includes
 *
 * ---------------------------------------------------------------------------*/

#ifndef RTS_STATIC_CLOSURES_H
#define RTS_STATIC_CLOSURES_H

#if CMINUSMINUS
#define STATIC_CLOSURE(clos) W_[clos ## _static_closure_ind]
#else
#define STATIC_CLOSURE(clos) (StgClosure*)(clos ## _static_closure_ind)
#endif

#define stg_END_TSO_QUEUE_closure STATIC_CLOSURE(stg_END_TSO_QUEUE)
#define stg_STM_AWOKEN_closure STATIC_CLOSURE(stg_STM_AWOKEN)
#define stg_NO_FINALIZER_closure STATIC_CLOSURE(stg_NO_FINALIZER)
#define stg_dummy_ret_closure STATIC_CLOSURE(stg_dummy_ret)
#define stg_forceIO_closure STATIC_CLOSURE(stg_forceIO)
#define stg_END_STM_WATCH_QUEUE_closure STATIC_CLOSURE(stg_END_STM_WATCH_QUEUE)
#define stg_END_INVARIANT_CHECK_QUEUE_closure STATIC_CLOSURE(stg_END_INVARIANT_CHECK_QUEUE)
#define stg_END_STM_CHUNK_LIST_closure STATIC_CLOSURE(stg_END_STM_CHUNK_LIST)
#define stg_NO_TREC_closure STATIC_CLOSURE(stg_NO_TREC)
#define stg_END_LISTENER_LIST_closure STATIC_CLOSURE(stg_END_LISTENER_LIST)

#ifndef CMINUSMINUS
typedef struct StaticClosureInds_ {
    StgClosure **start;
    StgClosure **end;
    struct StaticClosureInds_ *link;
} StaticClosureInds;

extern StaticClosureInds * RTS_VAR(SCI_LIST);

#define REGISTER_STATIC_CLOSURE_INDS(sci)               \
        do {                                            \
        if ((sci)->link == NULL) {                      \
            (sci)->link = SCI_LIST;                     \
            SCI_LIST = (sci);                           \
        }} while(0)

#endif

#endif /* RTS_STATIC_CLOSURES_H */
