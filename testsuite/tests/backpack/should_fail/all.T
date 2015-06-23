setTestOpts(only_compiler_types(['ghc']))

test('bkpfail01', normal, backpack_typecheck_fail, [''])
test('bkpfail02', normal, backpack_typecheck_fail, [''])
test('bkpfail03', normal, backpack_typecheck_fail, [''])
test('bkpfail04', normal, backpack_typecheck_fail, ['-ddump-shape'])
test('bkpfail05', normal, backpack_typecheck_fail, ['-ddump-shape'])
