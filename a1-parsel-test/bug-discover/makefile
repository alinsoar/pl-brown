
# MAKE NEW ``TEST.PSL`` in BUG_DISC_DIR

BUG_DISC_DIR=./bug-discover
TESTFILE=./test

test:
# *** make newtest FILE=test -C..  &
	make gentest TESTSUITEDIR=${BUG_DISC_DIR} FILE=${TESTFILE} -C..
	make test TESTSUITEDIR=${BUG_DISC_DIR} -C..

dotest:
# *** make newtest FILE=test -C..  &
	make testfile TESTSUITEDIR=${BUG_DISC_DIR} FILE=${TESTFILE} -C..



