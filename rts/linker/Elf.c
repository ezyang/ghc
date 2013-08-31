#if defined(OBJFORMAT_ELF)

#include <regex.h>    // regex is already used by dlopen() so this is OK
                      // to use here without requiring an additional lib

#include "linker/ElfMachO.h"

static void *dl_prog_handle;
static regex_t re_invalid;
static regex_t re_realso;

void initLinkerHelper(void)
{
    initLinkerHelper_ElfMachO();
}

void *lookupSymbolHelper(char *lbl)
{
    return internal_dlsym(dl_prog_handle, lbl);
}

#if defined(powerpc_HOST_ARCH) || defined(x86_64_HOST_ARCH)
#else
int ocAllocateSymbolExtras(ObjectCode *oc) {
    return 1;
}
#endif


#endif /* defined(OBJFORMAT_ELF) */
