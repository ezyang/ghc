setTestOpts(only_compiler_types(['ghc']))

test('bkpcabal01', normal, run_command, ['$MAKE -s --no-print-directory bkpcabal01'])
