#!/bin/bash
DIRECTORY="short-tests"
REFERENCE="out"
YASMV="./yasmv"

function test-unfeasible-state() {
    echo -n "Running short-test $1 ... "
    rm -f "$1.out"

    RES=$(YASMV_HOME=`pwd` $YASMV --quiet "$DIRECTORY/$1.smv" < "$DIRECTORY/unfeasible-pick-state.cmd" | tail -n1)
    if [[ $RES -eq "OK" ]]; then
	    echo "OK"
    else
        echo "FAILED!"
    	exit 1
    fi
}

# arrays
test-unfeasible-state array/array00

# enums
test-unfeasible-state enums/enum00

# casts
test-unfeasible-state casts/cast00
test-unfeasible-state casts/cast01
test-unfeasible-state casts/cast02
test-unfeasible-state casts/cast03

# ite
test-unfeasible-state ite/ite00
test-unfeasible-state ite/ite01

# nondet
test-unfeasible-state nondet/nondet00
test-unfeasible-state nondet/nondet01

# logical
test-unfeasible-state logical/logical00
test-unfeasible-state logical/logical01
test-unfeasible-state logical/logical02

echo ""  # one blank line
