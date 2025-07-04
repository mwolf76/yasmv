#!/bin/bash
# Script to compile C files to LLVM IR

if [ $# -eq 0 ]; then
    echo "Usage: $0 <file.c>"
    exit 1
fi

SOURCE=$1
BASE=$(basename "$SOURCE" .c)

# Compile to LLVM IR
clang -S -emit-llvm -O0 "$SOURCE" -o "${BASE}.ll"

echo "Generated ${BASE}.ll"
