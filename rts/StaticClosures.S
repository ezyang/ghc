/* mark stack as nonexecutable */
#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
/* does this even get ordered properly??? */
.section staticclosures,"aw"
    .p2align 16 /* max that the dynamic linker will respect */
