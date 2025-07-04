#!/bin/bash
# Script to compile C files to LLVM IR

if [ $# -eq 0 ]; then
    echo "Usage: $0 <file.c>"
    exit 1
fi

SOURCE=$1
BASE=$(basename "$SOURCE" .c)

# Check for clang - required for LLVM IR generation
if ! command -v clang >/dev/null 2>&1; then
    echo "Error: clang is required but not found."
    echo "Please install clang to compile C to LLVM IR:"
    echo "  sudo apt-get install clang     # Debian/Ubuntu"
    echo "  sudo yum install clang         # RedHat/CentOS"
    echo "  brew install llvm              # macOS"
    exit 1
fi

# Compile to LLVM IR
clang -S -emit-llvm -O0 "$SOURCE" -o "${BASE}.ll"
echo "Generated ${BASE}.ll"
