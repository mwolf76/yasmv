#!/bin/bash
EXAMPLES="examples"
YASMV="./yasmv"

function test() {
    local DIRECTORY="$1"
    local MODEL="$2"
    local COMMANDS="$3"
    local EXPECTED="$4"

    echo -n "Running functional test $DIRECTORY/$MODEL::$COMMANDS ... "
    rm -f "out"

    YASMV_HOME=`pwd` $YASMV --quiet "$EXAMPLES/$DIRECTORY/$MODEL" <"$EXAMPLES/$DIRECTORY/$COMMANDS" >out
    diff -wB "$EXAMPLES/$DIRECTORY/$EXPECTED" out &> /dev/null
    if [[ $? == 0 ]]; then
	    echo "OK"
            rm -f out
    else
        echo "FAILED!"
        echo "####### Showing EXPECTED and ACTUAL output for $DIRECTORY/$MODEL::$COMMANDS"
        diff -W $(( $(tput -T xterm cols) - 2 )) "$EXAMPLES/$DIRECTORY/$EXPECTED" out
    	exit 1
    fi
}

test cannibals cannibals.smv forward forward.out
test cannibals cannibals.smv backward backward.out

test maze solvable8x8.smv commands solvable8x8.out
test maze unsolvable8x8.smv commands unsolvable8x8.out
test maze solvable12x12.smv commands solvable12x12.out
test maze solvable16x16.smv commands solvable16x16.out

test vending vending.smv commands commands.out
test herschel herschel.smv commands commands.out
test koenisberg koenisberg.smv commands commands.out
test ferryman ferryman.smv commands commands.out
test fifteen fifteen.smv commands commands.out
test hanoi hanoi3.smv commands hanoi3.out
test magic magic.smv commands commands.out

echo ""  # one blank line
