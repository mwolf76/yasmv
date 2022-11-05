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

# enums
test-unfeasible-state enums/enum00

# casts
test-unfeasible-state casts/cast00
test-unfeasible-state casts/cast01
test-unfeasible-state casts/cast02
test-unfeasible-state casts/cast03

# ite
test-unfeasible-state ite/ite00

# nondet
test-unfeasible-state nondet/nondet00
test-unfeasible-state nondet/nondet01

echo ""  # one blank line
