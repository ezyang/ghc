setTestOpts(only_compiler_types(['ghc']))

test('backpack01',
     extra_clean(['dist']),
     run_command,
     ['$MAKE -s --no-print-directory backpack01'])
