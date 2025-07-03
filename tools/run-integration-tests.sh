#!/bin/bash
INTEGRATION="integration"
REFERENCE="out"
YASMV="./yasmv"

function test() {
    echo -n "Running integration test $1/$2 ... "
    rm -f "$2-out"

    res=$(YASMV_HOME=`pwd` $YASMV --quiet "$INTEGRATION/$1.smv" < "$INTEGRATION/$1.commands" | tail -n1)
    if [[ res -eq "OK" ]]; then
	    echo "OK"
    else
        echo "FAILED!"
    	exit 1
    fi
}

test enum00.smv enum00-pick-state.cmd
echo ""  # one blank line
