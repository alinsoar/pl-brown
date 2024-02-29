
BINDIR = ../debian-dist/bin/
GRADER = assignment3-debian

TEST_SUITE_DIR = suite

DESUGARER = typed-desugar-template.rkt

OPTIONS = ${DESUGARER} ./${TEST_SUITE_DIR}

test:
	${BINDIR}/${GRADER} --test-with-desugar ${OPTIONS}

brief:
	${BINDIR}/${GRADER} --brief --test-with-desugar ${OPTIONS}


normal:
	${BINDIR}/${GRADER} --test-with-normal ./${TEST_SUITE_DIR}

rep:
	${BINDIR}/${GRADER} --report ${DESUGARER}



