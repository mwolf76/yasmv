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

if ! python3 tests/test_functional_check.py; then
    echo "Functional checking tests FAILED"
    exit 1
fi

test magic magic.smv commands commands.out

echo ""  # one blank line
