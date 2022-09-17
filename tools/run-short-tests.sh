#!/bin/bash
DIRECTORY="short-tests"
REFERENCE="out"
YASMV="./yasmv"

function test() {
    echo -n "Running short-test $1/$2 ... "
    rm -f "$2-out"

    RES=$(YASMV_HOME=`pwd` $YASMV --quiet "$DIRECTORY/$1" < "$DIRECTORY/$2" | tail -n1)
    if [[ $RES -eq "OK" ]]; then
	    echo "OK"
    else
        echo "FAILED!"
    	exit 1
    fi
}

# enums
test enums/enum00.smv unfeasible-pick-state.cmd

# casts
test casts/cast00.smv unfeasible-pick-state.cmd
test casts/cast01.smv unfeasible-pick-state.cmd
test casts/cast02.smv unfeasible-pick-state.cmd

echo ""  # one blank line
