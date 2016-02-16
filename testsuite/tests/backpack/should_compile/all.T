setTestOpts(only_compiler_types(['ghc']))

test('bkpfile01', expect_broken(0), backpack_compile, ['-ddump-shape'])

test('bkp01', extra_clean(['bkp01_out/*']), backpack_compile, ['-ddump-shape -O'])
test('bkp01c', normal, run_command, ['$MAKE -s --no-print-directory bkp01c'])
test('bkp02', normal, backpack_compile, ['-ddump-shape'])
test('bkp03', normal, backpack_compile, ['-ddump-shape'])
test('bkp04', normal, backpack_compile, ['-ddump-shape'])
test('bkp05', expect_broken(0), backpack_compile, ['-ddump-shape']) # AvailInfo nonsense
test('bkp06', normal, backpack_compile, ['-ddump-shape']) # broken because we need to maintain signature dependency ordering
test('bkp07', normal, backpack_compile, ['-ddump-shape'])
test('bkp08', normal, backpack_compile, ['-ddump-shape'])
test('bkp09', expect_broken(0), backpack_compile, ['-ddump-shape']) # lots of stuff
test('bkp10', normal, backpack_compile, ['-ddump-shape'])
test('bkp11', expect_broken(0), backpack_compile, ['-ddump-shape'])
test('bkp12', normal, backpack_compile, ['-ddump-shape'])
test('bkp13', normal, backpack_compile, ['-ddump-shape'])
test('bkp14', normal, backpack_compile, ['-ddump-shape'])
test('bkp15', normal, backpack_compile, ['-ddump-shape'])
test('bkp16', normal, backpack_compile, ['']) # too chatty
test('bkp17', normal, backpack_compile, ['-ddump-shape'])
test('bkp18', normal, backpack_compile, ['-ddump-shape'])
test('bkp19', normal, backpack_compile, ['-ddump-shape'])
test('bkp20', expect_broken(0), backpack_compile, ['-ddump-shape']) # essentially dictionary
# missing: type classes
test('bkp21', normal, backpack_compile, ['-ddump-shape'])
# canonicalization, SCC-planning
test('bkp22', expect_broken(0), backpack_compile, ['-ddump-shape'])
test('bkp23', expect_broken(0), backpack_compile, ['-ddump-shape'])
