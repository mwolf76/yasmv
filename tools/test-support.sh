#!/bin/bash
# Shared runner: keep process status independent of semantic output.
YASMV=${YASMV:-./yasmv}
export YASMV_HOME=${YASMV_HOME:-$PWD}
YASMV_TEST_TIMEOUT=${YASMV_TEST_TIMEOUT:-60}
test_workdir=$(mktemp -d)
trap 'rm -rf "$test_workdir"' EXIT

run_yasmv_case() {
    local label=$1 model=$2 commands=$3 kind=$4 expected=$5 status actual
    printf 'Running %s ... ' "$label"
    timeout "$YASMV_TEST_TIMEOUT" "$YASMV" --quiet "$model" \
        < "$commands" > "$test_workdir/stdout" 2> "$test_workdir/stderr"
    status=$?
    if [[ $status -ne 0 ]]; then
        printf 'FAILED (checker exit %s)\n' "$status"
        cat "$test_workdir/stdout" "$test_workdir/stderr"
        return 1
    fi
    if [[ $kind == last ]]; then
        actual=$(tail -n 1 "$test_workdir/stdout" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')
        if [[ "$actual" != "$expected" ]]; then
            printf 'FAILED (expected %s, got %s)\n' "$expected" "$actual"
            cat "$test_workdir/stdout" "$test_workdir/stderr"
            return 1
        fi
    elif ! diff -wB "$expected" "$test_workdir/stdout" > "$test_workdir/diff"; then
        printf 'FAILED (output mismatch)\n'
        cat "$test_workdir/diff" "$test_workdir/stderr"
        return 1
    fi
    printf 'OK\n'
}
