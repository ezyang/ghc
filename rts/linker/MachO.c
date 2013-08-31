#if defined(OBJFORMAT_MACHO)

#include <regex.h>
#include <mach/machine.h>
#include <mach-o/fat.h>
#include <mach-o/loader.h>
#include <mach-o/nlist.h>
#include <mach-o/reloc.h>

#if !defined(HAVE_DLFCN_H)
#include <mach-o/dyld.h>
#endif

#if defined(powerpc_HOST_ARCH)
#include <mach-o/ppc/reloc.h>
#endif

#if defined(x86_64_HOST_ARCH)
#include <mach-o/x86_64/reloc.h>
#endif

#include "linker/ElfMachO.h"

#ifndef USE_MMAP
static int machoGetMisalignment( FILE * );
#endif

#ifdef powerpc_HOST_ARCH
static void machoInitSymbolsWithoutUnderscore( void );
#endif

void initLinkerHelper(void)
{
    initLinkerHelper_ElfMachO();
#if defined(powerpc_HOST_ARCH)
    machoInitSymbolsWithoutUnderscore();
#endif
}

void *lookupSymbolHelper(char *lbl)
{
#if HAVE_DLFCN_H
    /* On OS X 10.3 and later, we use dlsym instead of the old legacy
       interface.

       HACK: On OS X, all symbols are prefixed with an underscore.
             However, dlsym wants us to omit the leading underscore from the
             symbol name -- the dlsym routine puts it back on before searching
             for the symbol. For now, we simply strip it off here (and ONLY
             here).
    */
    IF_DEBUG(linker, debugBelch("lookupSymbol: looking up %s with dlsym\n", lbl));
    ASSERT(lbl[0] == '_');
    return internal_dlsym(dl_prog_handle, lbl + 1);
#else
    if (NSIsSymbolNameDefined(lbl)) {
        NSSymbol symbol = NSLookupAndBindSymbol(lbl);
        return NSAddressOfSymbol(symbol);
    } else {
        return NULL;
    }
#endif /* HAVE_DLFCN_H */
}

#if defined(powerpc_HOST_ARCH) || defined(x86_64_HOST_ARCH)
#else
int ocAllocateSymbolExtras(ObjectCode *oc) {
    return 1;
}
#endif


#endif /* defined(OBJFORMAT_MACHO) */
