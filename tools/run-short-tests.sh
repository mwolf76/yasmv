#!/bin/bash
DIRECTORY="short-tests"
REFERENCE="out"
YASMV="./yasmv"

function test() {
    echo -n "Running integration test $1/$2 ... "
    rm -f "$2-out"

    RES=$(YASMV_HOME=`pwd` $YASMV --quiet "$DIRECTORY/$1" < "$DIRECTORY/$2" | tail -n1)
    if [[ $RES -eq "OK" ]]; then
	    echo "OK"
    else
        echo "FAILED!"
    	exit 1
    fi
}

test enum00.smv enum00-pick-state.cmd
echo ""  # one blank line
