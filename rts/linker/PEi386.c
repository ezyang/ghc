#if defined(OBJFORMAT_PEi386)

#include <windows.h>
#include <math.h>

static void *lookupSymbolInDLLs ( unsigned char *lbl );
static void zapTrailingAtSign   ( unsigned char *sym );

void initLinkerHelper(void)
{
}

void exitLinkerHelper(void)
{
}

/* -----------------------------------------------------------------------------
 *                  Loading DLL dynamic libraries
 * -----------------------------------------------------------------------------
 *
 * Add a DLL from which symbols may be found.
 *
 * In the PEi386 case, open the DLLs and put handles to them in a
 * linked list.  When looking for a symbol, try all handles in the
 * list.  This means that we need to load even DLLs that are guaranteed
 * to be in the ghc.exe image already, just so we can get a handle
 * to give to loadSymbol, so that we can find the symbols.  For such
 * libraries, the LoadLibrary call should be a no-op except for returning
 * the handle.
 */

/* A record for storing handles into DLLs. */

typedef
   struct _OpenedDLL {
      pathchar*          name;
      struct _OpenedDLL* next;
      HINSTANCE instance;
   }
   OpenedDLL;

/* A list thereof. */
static OpenedDLL* opened_dlls = NULL;

const char *
addDLL( pathchar *dll_name )
{
   /* ------------------- Win32 DLL loader ------------------- */

   pathchar*      buf;
   OpenedDLL* o_dll;
   HINSTANCE  instance;

   initLinker();

   /* debugBelch("\naddDLL; dll_name = `%s'\n", dll_name); */

   /* See if we've already got it, and ignore if so. */
   for (o_dll = opened_dlls; o_dll != NULL; o_dll = o_dll->next) {
      if (0 == pathcmp(o_dll->name, dll_name))
         return NULL;
   }

   /* The file name has no suffix (yet) so that we can try
      both foo.dll and foo.drv

      The documentation for LoadLibrary says:
        If no file name extension is specified in the lpFileName
        parameter, the default library extension .dll is
        appended. However, the file name string can include a trailing
        point character (.) to indicate that the module name has no
        extension. */

   buf = stgMallocBytes((pathlen(dll_name) + 10) * sizeof(wchar_t), "addDLL");
   swprintf(buf, L"%s.DLL", dll_name);
   instance = LoadLibraryW(buf);
   if (instance == NULL) {
       if (GetLastError() != ERROR_MOD_NOT_FOUND) goto error;
       // KAA: allow loading of drivers (like winspool.drv)
       swprintf(buf, L"%s.DRV", dll_name);
       instance = LoadLibraryW(buf);
       if (instance == NULL) {
           if (GetLastError() != ERROR_MOD_NOT_FOUND) goto error;
           // #1883: allow loading of unix-style libfoo.dll DLLs
           swprintf(buf, L"lib%s.DLL", dll_name);
           instance = LoadLibraryW(buf);
           if (instance == NULL) {
               goto error;
           }
       }
   }
   stgFree(buf);

   /* Add this DLL to the list of DLLs in which to search for symbols. */
   o_dll = stgMallocBytes( sizeof(OpenedDLL), "addDLL" );
   o_dll->name     = pathdup(dll_name);
   o_dll->instance = instance;
   o_dll->next     = opened_dlls;
   opened_dlls     = o_dll;

   return NULL;

error:
   stgFree(buf);
   sysErrorBelch("%" PATH_FMT, dll_name);

   /* LoadLibrary failed; return a ptr to the error msg. */
   return "addDLL: could not load DLL";
}

void *lookupSymbolHelper(char *lbl)
{
    void* sym;

    sym = lookupSymbolInDLLs((unsigned char*)lbl);
    if (sym != NULL) { return sym; };

    // Also try looking up the symbol without the @N suffix.  Some
    // DLLs have the suffixes on their symbols, some don't.
    zapTrailingAtSign ( (unsigned char*)lbl );
    sym = lookupSymbolInDLLs((unsigned char*)lbl);
    if (sym != NULL) { return sym; };
    return NULL;
}

#endif /* defined(OBJFORMAT_PEi386) */
