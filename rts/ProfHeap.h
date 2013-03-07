/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2005
 *
 * Support for heap profiling
 *
 * ---------------------------------------------------------------------------*/

#ifndef PROFHEAP_H
#define PROFHEAP_H

#ifdef PROFILING
#include "sm/GC.h" // for evac_fn below
#endif

#include "BeginPrivate.h"

#ifdef PROFILING
// Listeners on the census, which fire when we take a census that crosses the limits
extern StgListener *census_listener_list;
void    markCensusListeners(evac_fn evac, void *user);
StgInt  queryCCS(CostCentreStack *ccs, StgWord type);
void    heapCensus         (Capability *cap, Time t);
#else
void    heapCensus         (Time t);
#endif
nat     initHeapProfiling  (void);
void    endHeapProfiling   (void);
rtsBool strMatchesSelector (char* str, char* sel);

#include "EndPrivate.h"

#endif /* PROFHEAP_H */
