#!/bin/bash
EXAMPLES="examples"
REFERENCE="out"
YASMV="./yasmv"

function test() {
    echo -n "Running functional test $1/$2 ... "
    rm -f "$2-out"

    YASMV_HOME=`pwd` $YASMV --quiet "$EXAMPLES/$1/$1.smv" < "$EXAMPLES/$1/commands.$2" > "$2-out"
    diff -wB "$REFERENCE/$2-out-ref" "$2-out" &> /dev/null
    if [[ $? == 0 ]]; then
	    echo "OK"
            rm -f "$2-out"
    else
        echo "FAILED!"
        echo "####### Showing EXPECTED and ACTUAL output for $1/$2"
        diff -W $(( $(tput cols) - 2 )) -y "$REFERENCE/$2-out-ref" "$2-out"
    	exit 1
    fi
}

test cannibals cannibals-forward
test cannibals cannibals-backward
test vending vending
test herschel herschel
test koenisberg koenisberg
test fifteen fifteen
test magic magic

echo ""  # one blank line
