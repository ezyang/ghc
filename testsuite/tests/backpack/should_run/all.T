setTestOpts(only_compiler_types(['ghc']))

test('bkprun01', normal, backpack_run, [''])
test('bkprun02', normal, backpack_run, [''])
test('bkprun03', normal, backpack_run, [''])
