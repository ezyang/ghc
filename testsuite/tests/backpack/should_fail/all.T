setTestOpts(only_compiler_types(['ghc']))

test('bkpfail01', normal, backpack_typecheck_fail, [''])
test('bkpfail03', normal, backpack_typecheck_fail, [''])
test('bkpfail04', normal, backpack_typecheck_fail, ['-ddump-shape'])
test('bkpfail05', normal, backpack_compile_fail, ['-ddump-shape'])
test('bkpfail06', normal, backpack_compile_fail, [''])
test('bkpfail07', expect_broken(0), backpack_typecheck_fail, ['']) # could fix this but not priority
