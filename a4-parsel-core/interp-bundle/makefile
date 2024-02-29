
BINARY = ../debian-dist/bin/assignment4-debian

TESTSUITEDIR=assignment4-suite/
TESTSUITEDIR2=assignment4-suite2/

OPTION_INTERP = --set-interp ./typed-interp-template.rkt
# OPTION_DESUGAR = --set-desugar ./typed-desugar-template.rkt

test:
	@${BINARY} \
	${OPTION_INTERP} \
	${OPTION_DESUGAR} \
	--test ${TESTSUITEDIR}

test2:
	@${BINARY} \
	${OPTION_INTERP} \
	${OPTION_DESUGAR} \
	--test ${TESTSUITEDIR2}





