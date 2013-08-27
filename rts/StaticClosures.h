#ifndef STATIC_CLOSURES_H
#define STATIC_CLOSURES_H

#include "BeginPrivate.h"
#include "Rts.h"

void initStaticClosures(void);
void processStaticClosures(void);
void checkStaticClosures(StgClosure**, StgClosure**);
W_ countStaticBlocks(void);

#include "EndPrivate.h"

#endif /* STATIC_CLOSURES_H */
