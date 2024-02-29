
TESTSUITEDIR=./test-suite/
TESTPROGSDIR=./test-programs/
EXECDIR=./debian-dist

PSLX=${EXECDIR}/bin/psl
XX=${EXECDIR}/bin/assignment1-debian

test:
	${XX} --brief ${TESTSUITEDIR}

single:
# *** make single INTR='functions1' -C.. &
	${XX} --single ${INTR} ${TESTSUITEDIR}

testfile:
# *** make testfile FILE=test  -C..  &
	${XX} --interp < ${TESTSUITEDIR}/${FILE}.psl

testi:
	${XX} --test-interps ${TESTSUITEDIR}

rep:
	${XX} --report ${TESTSUITEDIR}

psl:
# *** make psl FILE=fibs -C.. &
	@echo RUN TEST PROGRAM ${FILE}.psl
	${PSLX} ${TESTPROGSDIR}/${FILE}.psl

gentest:
# *** make gentest FILE=add-strings -C..  &
	${XX} --interp                            \
	<${TESTSUITEDIR}/${FILE}.psl               \
	1> ${TESTSUITEDIR}/${FILE}.psl.expected    \
	2> ${TESTSUITEDIR}/${FILE}.psl.error


