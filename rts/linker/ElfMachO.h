#ifdef LINKER_ELFMACHO_H

#error "linker/ElfMachO.h can only be included once from a C file"

#else

#define LINKER_ELFMACHO_H

#if defined(OBJFORMAT_MACHO) || defined(OBJFORMAT_ELF)

#ifdef THREADED_RTS
#include "Rts.h"
static Mutex dl_mutex; // mutex to protect dlopen/dlerror critical section
#endif

static void *dl_prog_handle;
static regex_t re_invalid;
static regex_t re_realso;

static void init_dl_prog_handle(void);
void init_re(void);

static void initLinkerHelper_ElfMachO(void) {
    int compileResult;

#if defined(THREADED_RTS)
    initMutex(&dl_mutex);
#endif

#if defined(RTLD_DEFAULT)
    dl_prog_handle = RTLD_DEFAULT;
#else
    dl_prog_handle = dlopen(NULL, RTLD_LAZY);
#endif /* RTLD_DEFAULT */

    compileResult = regcomp(&re_invalid,
           "(([^ \t()])+\\.so([^ \t:()])*):([ \t])*(invalid ELF header|file too short)",
           REG_EXTENDED);
    if (compileResult != 0) {
        barf("Compiling re_invalid failed");
    }
    compileResult = regcomp(&re_realso,
           "(GROUP|INPUT) *\\( *([^ )]+)",
           REG_EXTENDED);
    if (compileResult != 0) {
        barf("Compiling re_realso failed");
    }
}

void exitLinkerHelper(void)
{
      regfree(&re_invalid);
      regfree(&re_realso);
#ifdef THREADED_RTS
      closeMutex(&dl_mutex);
#endif
}


/* -----------------------------------------------------------------------------
 *                  Loading .so dynamic libraries
 * -----------------------------------------------------------------------------
 *
 * Add a DLL from which symbols may be found.  In the ELF case, just
 * do RTLD_GLOBAL-style add, so no further messing around needs to
 * happen in order that symbols in the loaded .so are findable --
 * lookupSymbol() will subsequently see them by dlsym on the program's
 * dl-handle.  Returns NULL if success, otherwise ptr to an err msg.
 */

/* Suppose in ghci we load a temporary SO for a module containing
       f = 1
   and then modify the module, recompile, and load another temporary
   SO with
       f = 2
   Then as we don't unload the first SO, dlsym will find the
       f = 1
   symbol whereas we want the
       f = 2
   symbol. We therefore need to keep our own SO handle list, and
   try SOs in the right order. */

typedef
   struct _OpenedSO {
      struct _OpenedSO* next;
      void *handle;
   }
   OpenedSO;

/* A list thereof. */
static OpenedSO* openedSOs = NULL;

static const char *
internal_dlopen(const char *dll_name)
{
   OpenedSO* o_so;
   void *hdl;
   const char *errmsg;
   char *errmsg_copy;

   // omitted: RTLD_NOW
   // see http://www.haskell.org/pipermail/cvs-ghc/2007-September/038570.html
   IF_DEBUG(linker,
      debugBelch("internal_dlopen: dll_name = '%s'\n", dll_name));

   //-------------- Begin critical section ------------------
   // This critical section is necessary because dlerror() is not
   // required to be reentrant (see POSIX -- IEEE Std 1003.1-2008)
   // Also, the error message returned must be copied to preserve it
   // (see POSIX also)

   ACQUIRE_LOCK(&dl_mutex);
   hdl = dlopen(dll_name, RTLD_LAZY | RTLD_GLOBAL);

   errmsg = NULL;
   if (hdl == NULL) {
      /* dlopen failed; return a ptr to the error msg. */
      errmsg = dlerror();
      if (errmsg == NULL) errmsg = "addDLL: unknown error";
      errmsg_copy = stgMallocBytes(strlen(errmsg)+1, "addDLL");
      strcpy(errmsg_copy, errmsg);
      errmsg = errmsg_copy;
   }
   o_so = stgMallocBytes(sizeof(OpenedSO), "addDLL");
   o_so->handle = hdl;
   o_so->next   = openedSOs;
   openedSOs    = o_so;

   RELEASE_LOCK(&dl_mutex);
   //--------------- End critical section -------------------

   return errmsg;
}

static void *
internal_dlsym(void *hdl, const char *symbol) {
    OpenedSO* o_so;
    void *v;

    // We acquire dl_mutex as concurrent dl* calls may alter dlerror
    ACQUIRE_LOCK(&dl_mutex);
    dlerror();
    for (o_so = openedSOs; o_so != NULL; o_so = o_so->next) {
        v = dlsym(o_so->handle, symbol);
        if (dlerror() == NULL) {
            RELEASE_LOCK(&dl_mutex);
            return v;
        }
    }
    v = dlsym(hdl, symbol)
    RELEASE_LOCK(&dl_mutex);
    return v;
}

const char *
addDLL( pathchar *dll_name )
{
   /* ------------------- ELF DLL loader ------------------- */

#define NMATCH 5
   regmatch_t match[NMATCH];
   const char *errmsg;
   FILE* fp;
   size_t match_length;
#define MAXLINE 1000
   char line[MAXLINE];
   int result;

   initLinker();

   IF_DEBUG(linker, debugBelch("addDLL: dll_name = '%s'\n", dll_name));
   errmsg = internal_dlopen(dll_name);

   if (errmsg == NULL) {
      return NULL;
   }

   // GHC Trac ticket #2615
   // On some systems (e.g., Gentoo Linux) dynamic files (e.g. libc.so)
   // contain linker scripts rather than ELF-format object code. This
   // code handles the situation by recognizing the real object code
   // file name given in the linker script.
   //
   // If an "invalid ELF header" error occurs, it is assumed that the
   // .so file contains a linker script instead of ELF object code.
   // In this case, the code looks for the GROUP ( ... ) linker
   // directive. If one is found, the first file name inside the
   // parentheses is treated as the name of a dynamic library and the
   // code attempts to dlopen that file. If this is also unsuccessful,
   // an error message is returned.

   // see if the error message is due to an invalid ELF header
   IF_DEBUG(linker, debugBelch("errmsg = '%s'\n", errmsg));
   result = regexec(&re_invalid, errmsg, (size_t) NMATCH, match, 0);
   IF_DEBUG(linker, debugBelch("result = %i\n", result));
   if (result == 0) {
      // success -- try to read the named file as a linker script
      match_length = (size_t) stg_min((match[1].rm_eo - match[1].rm_so),
                                 MAXLINE-1);
      strncpy(line, (errmsg+(match[1].rm_so)),match_length);
      line[match_length] = '\0'; // make sure string is null-terminated
      IF_DEBUG(linker, debugBelch ("file name = '%s'\n", line));
      if ((fp = fopen(line, "r")) == NULL) {
         return errmsg; // return original error if open fails
      }
      // try to find a GROUP or INPUT ( ... ) command
      while (fgets(line, MAXLINE, fp) != NULL) {
         IF_DEBUG(linker, debugBelch("input line = %s", line));
         if (regexec(&re_realso, line, (size_t) NMATCH, match, 0) == 0) {
            // success -- try to dlopen the first named file
            IF_DEBUG(linker, debugBelch("match%s\n",""));
            line[match[2].rm_eo] = '\0';
            errmsg = internal_dlopen(line+match[2].rm_so);
            break;
         }
         // if control reaches here, no GROUP or INPUT ( ... ) directive
         // was found and the original error message is returned to the
         // caller
      }
      fclose(fp);
   }
   return errmsg;
}

/* --------------------------------------------------------------------------
 * Symbol Extras.
 * This is about allocating a small chunk of memory for every symbol in the
 * object file. We make sure that the SymboLExtras are always "in range" of
 * limited-range PC-relative instructions on various platforms by allocating
 * them right next to the object code itself.
 */

#if defined(powerpc_HOST_ARCH) || defined(x86_64_HOST_ARCH) || defined(arm_HOST_ARCH)
#if !defined(x86_64_HOST_ARCH) || !defined(mingw32_HOST_OS)

/*
  ocAllocateSymbolExtrasHelper

  Allocate additional space at the end of the object file image to make room
  for jump islands (powerpc, x86_64, arm) and GOT entries (x86_64).

  PowerPC relative branch instructions have a 24 bit displacement field.
  As PPC code is always 4-byte-aligned, this yields a +-32MB range.
  If a particular imported symbol is outside this range, we have to redirect
  the jump to a short piece of new code that just loads the 32bit absolute
  address and jumps there.
  On x86_64, PC-relative jumps and PC-relative accesses to the GOT are limited
  to 32 bits (+-2GB).

  This function just allocates space for one SymbolExtra for every
  undefined symbol in the object file. The code for the jump islands is
  filled in by makeSymbolExtra below.
*/

static int ocAllocateSymbolExtrasHelper( ObjectCode* oc, int count, int first )
{
#ifdef USE_MMAP
  int pagesize, n, m;
#endif
  int aligned;
#ifndef USE_MMAP
  int misalignment = 0;
#ifdef darwin_HOST_OS
  misalignment = oc->misalignment;
#endif
#endif

  if( count > 0 )
  {
    // round up to the nearest 4
    aligned = (oc->fileSize + 3) & ~3;

#ifdef USE_MMAP
    pagesize = getpagesize();
    n = ROUND_UP( oc->fileSize, pagesize );
    m = ROUND_UP( aligned + sizeof (SymbolExtra) * count, pagesize );

    /* we try to use spare space at the end of the last page of the
     * image for the jump islands, but if there isn't enough space
     * then we have to map some (anonymously, remembering MAP_32BIT).
     */
    if( m > n ) // we need to allocate more pages
    {
        if (USE_CONTIGUOUS_MMAP)
        {
            /* Keep image and symbol_extras contiguous */
            void *new = mmapForLinker(n + (sizeof(SymbolExtra) * count),
                                  MAP_ANONYMOUS, -1);
            if (new)
            {
                memcpy(new, oc->image, oc->fileSize);
                munmap(oc->image, n);
                oc->image = new;
                oc->fileSize = n + (sizeof(SymbolExtra) * count);
                oc->symbol_extras = (SymbolExtra *) (oc->image + n);
            }
            else
                oc->symbol_extras = NULL;
        }
        else
        {
            oc->symbol_extras = mmapForLinker(sizeof(SymbolExtra) * count,
                                          MAP_ANONYMOUS, -1);
        }
    }
    else
    {
        oc->symbol_extras = (SymbolExtra *) (oc->image + aligned);
    }
#else
    oc->image -= misalignment;
    oc->image = stgReallocBytes( oc->image,
                                 misalignment +
                                 aligned + sizeof (SymbolExtra) * count,
                                 "ocAllocateSymbolExtrasHelper" );
    oc->image += misalignment;

    oc->symbol_extras = (SymbolExtra *) (oc->image + aligned);
#endif /* USE_MMAP */

    memset( oc->symbol_extras, 0, sizeof (SymbolExtra) * count );
  }
  else
    oc->symbol_extras = NULL;

  oc->first_symbol_extra = first;
  oc->n_symbol_extras = count;

  return 1;
}

#endif
#endif // defined(powerpc_HOST_ARCH) || defined(x86_64_HOST_ARCH) || defined(arm_HOST_ARCH)

#endif /* defined(OBJFORMAT_MACHO) || defined(OBJFORMAT_ELF) */

#endif /* defined(LINKER_ELFMACHO_H) */
