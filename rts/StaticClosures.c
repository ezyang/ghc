/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2013
 *
 * Responsible for copying static closures into proper blocks so that
 * bdescr works.
 *
 * ---------------------------------------------------------------------------*/

#include "Rts.h"

StaticClosureInds *SCI_LIST = NULL;
