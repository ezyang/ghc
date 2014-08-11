if default_testopts.cleanup != '':
   cleanup = 'CLEANUP=1'
else:
   cleanup = ''

test('cabal07',
     normal,
     run_command,
     ['$MAKE -s --no-print-directory cabal07 ' + cleanup])
