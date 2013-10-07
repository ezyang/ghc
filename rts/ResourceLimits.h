#ifndef RESOURCE_LIMITS_H
#define RESOURCE_LIMITS_H

#include "sm/GCThread.h"

#include "BeginPrivate.h"

// NB: keep this size something nice...
typedef struct rcthread_ {
    bdescr *currentNursery;
    nursery nursery;
    gen_workspace *workspaces;
} rcthread;

typedef struct ResourceContainer_ {
    char *label;
    struct ResourceContainer_ *link;
    struct ResourceContainer_ *parent;
    memcount max_blocks;
    memcount used_blocks;
    rcthread threads[FLEXIBLE_ARRAY];
} ResourceContainer;

void initResourceLimits(void);
ResourceContainer *newResourceContainer(nat max_blocks, ResourceContainer *parent);

#include "EndPrivate.h"

#endif /* RESOURCE_LIMITS_H */
