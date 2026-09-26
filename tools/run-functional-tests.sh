#!/bin/bash
EXAMPLES="examples"
source "$(dirname "${BASH_SOURCE[0]}")/test-support.sh"

function test() {
    local DIRECTORY="$1"
    local MODEL="$2"
    local COMMANDS="$3"
    local EXPECTED="$4"

    run_yasmv_case "functional test $DIRECTORY/$MODEL::$COMMANDS" \
        "$EXAMPLES/$DIRECTORY/$MODEL" "$EXAMPLES/$DIRECTORY/$COMMANDS" \
        file "$EXAMPLES/$DIRECTORY/$EXPECTED" || exit 1
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
