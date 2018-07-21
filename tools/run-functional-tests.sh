#!/bin/bash
EXAMPLES="examples"
YASMV="./yasmv"

function test() {
    diff $1-out "$EXAMPLES/$1/$1-out-ref"
    if [ $? == 0 ]; then
	echo "### $1 ok"
    else
    	exit 1
    fi
}

YASMV_HOME=`pwd` $YASMV --quiet "$EXAMPLES/cannibals/cannibals.smv" < "$EXAMPLES/cannibals/commands" > cannibals-out
test cannibals

YASMV_HOME=`pwd` $YASMV --quiet "$EXAMPLES/vending/vending.smv" < "$EXAMPLES/vending/commands" > vending-out
test vending

YASMV_HOME=`pwd` $YASMV --quiet "$EXAMPLES/herschel/herschel.smv" < "$EXAMPLES/herschel/commands" > herschel-out
test herschel

YASMV_HOME=`pwd` $YASMV --quiet "$EXAMPLES/koenisberg/koenisberg.smv" < "$EXAMPLES/koenisberg/commands" > koenisberg-out
test koenisberg

