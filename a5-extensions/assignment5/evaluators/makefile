
TEST="../tests/exn-scope-tests/${TEST_FILE}.psl"

test:
	@if  [ ! -f "${TEST}" ] ; then\
	  echo "TEST_FILE missing";\
	  echo "use so: make TEST_FILE=file";\
	  echo "- - - - - - - - - - available test files";\
	  ls -1 ../tests/exn-scope-tests/*.psl |\
	  xargs -i@  basename -s .psl @;\
	  echo;\
	  exit 1;\
	else\
	 echo "TEST" ${TEST_FILE};\
	 echo "RUN:" racket\
	 ../parseltongue-lang/extensions-assignment-main.rkt\
	 --stdin ${TEST}\
	 --set-evaluator exn-evaluator.rkt\
	 --interp;\
	 echo;\
	 racket\
	 ../parseltongue-lang/extensions-assignment-main.rkt\
	 --stdin ${TEST}\
	 --set-evaluator exn-evaluator.rkt\
	 --interp;\
	fi

all_tests:
	@racket\
	 ../parseltongue-lang/extensions-assignment-main.rkt\
	 --test ../tests/exn-scope-tests/\
	 --set-evaluator exn-evaluator.rkt

test_suite:
	@racket\
	 ../parseltongue-lang/extensions-assignment-main.rkt\
	 --test ../tests/test-suite/\
	 --set-evaluator exn-evaluator.rkt

make:
	raco make ../parseltongue-lang/extensions-assignment-main.rkt

tags:
	@etags *.rkt # ../parseltongue-lang/*.rkt



