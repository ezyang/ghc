setTestOpts(only_compiler_types(['ghc']))

# For now, these all fail, but they will stop failing if we gain
# support for mutual recursion

test('bkprec01', normal, backpack_typecheck_fail, [''])
