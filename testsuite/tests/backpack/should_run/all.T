setTestOpts(only_compiler_types(['ghc']))

test('bkprun01', normal, backpack_run, [''])
