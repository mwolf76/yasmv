#!/bin/bash
DIRECTORY="short-tests"
REFERENCE="out"
YASMV="./yasmv"

function test-unfeasible-state() {
    echo -n "Running short-test $1 ... "
    rm -f "$1.out"

    RES=$(YASMV_HOME=`pwd` $YASMV --quiet "$DIRECTORY/$1" < "$DIRECTORY/unfeasible-pick-state.cmd" | tail -n1)
    if [[ $RES -eq "OK" ]]; then
	    echo "OK"
    else
        echo "FAILED!"
    	exit 1
    fi
}

# arrays
test-unfeasible-state arrays/array00.smv

# enums
test-unfeasible-state enums/enum00.smv

# casts
test-unfeasible-state casts/cast00.smv
test-unfeasible-state casts/cast01.smv
test-unfeasible-state casts/cast02.smv
test-unfeasible-state casts/cast03.smv

# ite
test-unfeasible-state ite/ite00.smv
test-unfeasible-state ite/ite01.smv

# nondet
test-unfeasible-state nondet/nondet00.smv
test-unfeasible-state nondet/nondet01.smv

# logical
test-unfeasible-state logical/logical00.smv
test-unfeasible-state logical/logical01.smv
test-unfeasible-state logical/logical02.smv

echo ""  # one blank line
