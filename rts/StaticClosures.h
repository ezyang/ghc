#ifndef STATIC_CLOSURES_H
#define STATIC_CLOSURES_H

#include "BeginPrivate.h"
#include "Rts.h"

void initStaticClosures(void);
void processStaticClosures(StaticClosureInds *, bdescr **);
void allocateStaticClosures(StaticClosureInds *, bdescr **);
void updateStaticClosureFields(StaticClosureInds *);
W_ countStaticBlocks(void);

#ifdef DEBUG
void checkStaticClosures(W_ size_b, StgClosure**);
#endif

typedef struct
{
    union {
        const StgInfoTable* tagged_info;
        StgClosure *dest;
    } t;
#ifdef PROFILING
    CostCentreStack *ccs;
#endif
    struct StgClosure_ *payload[FLEXIBLE_ARRAY];
} StgStaticClosureDesc;

#include "EndPrivate.h"

#endif /* STATIC_CLOSURES_H */
