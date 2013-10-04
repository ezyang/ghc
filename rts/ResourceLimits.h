#ifndef RESOURCE_LIMITS_H
#define RESOURCE_LIMITS_H

#include "BeginPrivate.h"

void initResourceLimits(void);
ResourceContainer *newResourceContainer(void);

rtsBool allocGroupFor(bdescr **, W_ n, ResourceContainer *);
rtsBool allocBlockFor(bdescr **, ResourceContainer *);

#include "EndPrivate.h"

#endif /* RESOURCE_LIMITS_H */
