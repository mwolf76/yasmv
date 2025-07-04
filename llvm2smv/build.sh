#!/bin/bash
# Simple build script for llvm2smv

set -e

echo "=== Building llvm2smv ==="

# Check if LLVM is available
if ! command -v llvm-config &> /dev/null && \
   ! command -v llvm-config-15 &> /dev/null && \
   ! command -v llvm-config-14 &> /dev/null && \
   ! command -v llvm-config-13 &> /dev/null && \
   ! command -v llvm-config-12 &> /dev/null && \
   ! command -v llvm-config-11 &> /dev/null && \
   ! command -v llvm-config-10 &> /dev/null; then
    echo "ERROR: LLVM not found!"
    echo "Please install LLVM development packages:"
    echo "  Ubuntu/Debian: sudo apt-get install llvm-dev clang build-essential"
    echo "  CentOS/RHEL:   sudo yum install llvm-devel clang"
    echo "  Arch:          sudo pacman -S llvm clang"
    exit 1
fi

# Check for C++20 support
echo "Checking C++20 compiler support..."
echo "int main(){}" | g++ -std=c++20 -x c++ - -o /tmp/cxx20test 2>/dev/null && rm -f /tmp/cxx20test || {
    echo "ERROR: C++20 support not found!"
    echo "Please install a modern compiler:"
    echo "  Ubuntu/Debian: sudo apt-get install g++-10 (or newer)"
    echo "  Or use clang++:  sudo apt-get install clang-10 (or newer)"
    exit 1
}

# Show build info
echo "Checking dependencies..."
make deps

echo ""
echo "Building..."
make clean
make

echo ""
echo "Testing..."
make test

echo ""
echo "=== Build complete! ==="
echo "Run './llvm2smv --help' for usage information"
