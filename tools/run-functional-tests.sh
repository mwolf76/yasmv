#!/bin/bash
EXAMPLES="examples"
YASMV="./yasmv"

function test() {
    diff $1-out "$EXAMPLES/$1/$1-out-ref"
    if [ $? == 0 ]; then
	echo "-- $1 ok"
    else
    	exit 1
    fi
}

yasmv --quiet "$EXAMPLES/cannibals/cannibals.smv" < "$EXAMPLES/cannibals/commands" > cannibals-out
test cannibals

yasmv --quiet "$EXAMPLES/vending/vending.smv" < "$EXAMPLES/vending/commands" > vending-out
test vending

yasmv --quiet "$EXAMPLES/herschel/herschel.smv" < "$EXAMPLES/herschel/commands" > herschel-out
test herschel

yasmv --quiet "$EXAMPLES/koenisberg/koenisberg.smv" < "$EXAMPLES/koenisberg/commands" > koenisberg-out
test koenisberg

