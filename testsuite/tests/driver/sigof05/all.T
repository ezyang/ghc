test('sigof05',
     [ clean_cmd('rm -rf tmp_sigof05') ],
     run_command,
     ['$MAKE -s --no-print-directory sigof05'])

test('sigof05f',
     [ clean_cmd('rm -rf tmp_sigof05f') ],
     run_command,
     ['$MAKE -s --no-print-directory sigof05f'])

test('sigof05m',
     [ clean_cmd('rm -rf tmp_sigof05m') ],
     run_command,
     ['$MAKE -s --no-print-directory sigof05m'])

test('sigof05fm',
     [ clean_cmd('rm -rf tmp_sigof05fm') ],
     run_command,
     ['$MAKE -s --no-print-directory sigof05fm'])
