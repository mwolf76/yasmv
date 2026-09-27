#!/usr/bin/env bash
# Configure/build the translator through the repository's Autotools build.
set -euo pipefail
repo_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_dir"
autoreconf -vif
./configure --enable-llvm2smv "$@"
make -C llvm2smv
make -C llvm2smv test
