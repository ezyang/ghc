setTestOpts(only_compiler_types(['ghc']))

# This fails, because you need some sort of progressive shaping
# to figure these out correctly.  In principle we should be
# able to implement this, but if you rule out signature
# reexports these should not be allowed

test('bkpreex01', normal, backpack_typecheck_fail, [''])
test('bkpreex02', normal, backpack_typecheck_fail, [''])
test('bkpreex03', normal, backpack_typecheck_fail, [''])
