#!/usr/bin/env bash
# Compile with the selected LLVM 18 Clang; do not hide compiler failures.
set -euo pipefail
if [[ $# -lt 1 || $# -gt 2 ]]; then
    echo "Usage: $0 source.c [output.ll]" >&2
    exit 2
fi
compiler=${CLANG:-clang-18}
compiler_version=$("$compiler" --version)
if [[ ! "$compiler_version" =~ version\ 18\. ]]; then
    echo "Error: llvm2smv requires Clang 18; set CLANG to the configured compiler." >&2
    exit 2
fi
source_file=$1
output_file=${2:-$(basename -- "$source_file" .c).ll}
"$compiler" -S -emit-llvm -O0 -g -fno-finite-loops "$source_file" -o "$output_file"
echo "Generated $output_file"
