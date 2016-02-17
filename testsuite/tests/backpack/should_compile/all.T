setTestOpts(only_compiler_types(['ghc']))

test('bkpfile01', expect_broken(0), backpack_compile, ['-ddump-shape'])

test('bkp01', extra_clean(['bkp01_out/*']), backpack_compile, ['-ddump-shape -O'])
test('bkp01c', normal, run_command, ['$MAKE -s --no-print-directory bkp01c'])
test('bkp02', normal, backpack_compile, ['-ddump-shape'])
test('bkp04', normal, backpack_compile, ['-ddump-shape'])
# Fails due to AvailInfo nonsense
test('bkp05', normal, backpack_compile_fail, ['-ddump-shape'])
test('bkp06', normal, backpack_compile, ['-ddump-shape'])
test('bkp07', normal, backpack_compile, ['-ddump-shape'])
test('bkp08', normal, backpack_compile, ['-ddump-shape'])
test('bkp09', normal, backpack_compile, ['-ddump-shape'])
test('bkp10', normal, backpack_compile, ['-ddump-shape'])
# Duplicate renaming destination, planning to implement later
test('bkp11', normal, backpack_compile_fail, ['-ddump-shape'])
test('bkp12', normal, backpack_compile, ['-ddump-shape'])
test('bkp13', normal, backpack_compile, ['-ddump-shape'])
test('bkp14', normal, backpack_compile, ['-ddump-shape'])
test('bkp15', normal, backpack_compile, ['-ddump-shape'])
test('bkp16', normal, backpack_compile, ['']) # too chatty
test('bkp17', normal, backpack_compile, ['-ddump-shape'])
test('bkp18', normal, backpack_compile, ['-ddump-shape'])
test('bkp19', normal, backpack_compile, ['-ddump-shape'])
test('bkp20', normal, backpack_compile, ['-ddump-shape'])
test('bkp21', normal, backpack_compile, ['-ddump-shape'])
# Canonicalization, SCC-planning
test('bkp22', normal, backpack_compile_fail, ['-ddump-shape'])
test('bkp23', normal, backpack_compile, ['-ddump-shape'])
