#!/bin/sh
#
# Copyright (C) 2016 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
#
# This library is free software; you can redistribute it and/or
# modify it under the terms of the GNU Lesser General Public
# License as published by the Free Software Foundation; either
# version 2.1 of the License, or (at your option) any later version.
#
# This library is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more
# details.
#
# You should have received a copy of the GNU Lesser General Public
# License along with this library; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
#

set -e

# Work relative to the checkout, including when invoked from another directory.
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"

# Use available processors for dependency and project builds.
setup_jobs=
if command -v nproc >/dev/null 2>&1; then
    setup_jobs=$(nproc) || setup_jobs=
fi
case $setup_jobs in
    ''|0|*[!0-9]*) setup_jobs= ;;
esac
setup_make() {
    if [ -n "$setup_jobs" ]; then
        make -j "$setup_jobs" "$@"
    else
        make "$@"
    fi
}

# set to 1 to enable distcc compilation
USE_DISTCC=0

# set to 1 to make a debugger-friendly build
USE_DEBUGGER=0

# set to 1 to enable strict compilation settings
USE_STRICT=1

# a few useful standard defines
DEFINES="-D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -DPIC"

if [ $USE_DISTCC -eq 1 ];
then
    CC="distcc gcc"
    CXX="distcc g++"
else
    CC="gcc"
    CXX="g++"
fi

COMMON_OPTIONS="-fPIC -std=c++20"

if [ $USE_DEBUGGER -eq 1 ];
then
    # compilation options for debugging, all + extra warnings enabled. Any warning is fatal.
    OPTIONS="-g -O0"
else
    # optimized production build; CaDiCaL has its own release compiler flags.
    OPTIONS="-O2"
fi

if [ $USE_STRICT -eq 1 ];
then
    # compilation options for debugging, all + extra warnings enabled. Any warning is fatal.
    FLAGS="-Wall -Wno-deprecated-declarations -Werror"
else
    # compilation options for debugging, all + extra warnings enabled. Any warning is fatal.
    FLAGS=""
fi

SETTINGS="$DEFINES $COMMON_OPTIONS $OPTIONS $FLAGS"

# An explicit external prefix opts out of the local dependency bootstrap.
# Keep the compiler selection consistent with configure's last-argument wins.
cadical_prefix=${CADICAL_PREFIX:-}
cadical_cc=$CC
cadical_cxx=$CXX
cadical_prefix_next=no
for setup_argument do
    if [ "$cadical_prefix_next" = yes ]; then
        cadical_prefix=$setup_argument
        cadical_prefix_next=no
        continue
    fi
    case $setup_argument in
        --with-cadical-prefix=*) cadical_prefix=${setup_argument#*=} ;;
        --with-cadical-prefix) cadical_prefix_next=yes ;;
        CC=*) cadical_cc=${setup_argument#*=} ;;
        CXX=*) cadical_cxx=${setup_argument#*=} ;;
    esac
done
if [ "$cadical_prefix_next" = yes ]; then
    printf '%s\n' 'setup: --with-cadical-prefix needs a path' >&2
    exit 1
fi

if [ -z "$cadical_prefix" ]; then
    cadical_revision=c60730422e758ef1cebe7aeddf2dda31c996bf04
    cadical_source="$PWD/.deps/cadical-$cadical_revision"
    cadical_prefix="$cadical_source/prefix"
    if [ ! -d "$cadical_source" ]; then
        mkdir -p "$PWD/.deps"
        # Clone into a staging directory: an interrupted download must not be
        # mistaken for a reusable checkout on the next invocation.
        cadical_stage=$(mktemp -d "$PWD/.deps/cadical-fetch.XXXXXX")
        GIT_TERMINAL_PROMPT=0 git clone --depth 1 --branch rel-3.0.1 \
            https://github.com/arminbiere/cadical.git "$cadical_stage/source"
        mv "$cadical_stage/source" "$cadical_source"
        rmdir "$cadical_stage"
    fi
    if [ "$(git -C "$cadical_source" rev-parse HEAD)" != "$cadical_revision" ] ||
       ! git -C "$cadical_source" diff --quiet HEAD --; then
        printf '%s\n' 'setup: cached CaDiCaL source is not the unmodified pinned revision' >&2
        exit 1
    fi

    # Cache only complete builds made with the selected compiler and release
    # flags. Do not leak yasmv's CXXFLAGS into the native solver build.
    cadical_cc_version=$($cadical_cc --version)
    cadical_cxx_version=$($cadical_cxx --version)
    cadical_build_config=$(printf '%s\n' "$cadical_revision" "$cadical_cc" \
        "$cadical_cxx" "$cadical_cc_version" "$cadical_cxx_version" '-O3 -DNDEBUG -fPIC')
    if [ ! -f "$cadical_prefix/lib/libcadical.a" ] ||
       [ ! -f "$cadical_prefix/include/cadical.hpp" ] ||
       [ ! -f "$cadical_prefix/include/tracer.hpp" ] ||
       [ ! -f "$cadical_prefix/.yasmv-build-config" ] ||
       [ "$(cat "$cadical_prefix/.yasmv-build-config")" != "$cadical_build_config" ]; then
        printf '%s\n' 'Building the pinned CaDiCaL release dependency ...'
        # An interrupted rebuild/install must not leave a valid cache marker.
        rm -f "$cadical_prefix/.yasmv-build-config"
        (cd "$cadical_source" && \
            CC="$cadical_cc" CXX="$cadical_cxx" CFLAGS= CXXFLAGS= ./configure -fPIC)
        setup_make -C "$cadical_source/build" libcadical.a
        mkdir -p "$cadical_prefix/include" "$cadical_prefix/lib"
        install -m 644 "$cadical_source/src/cadical.hpp" "$cadical_source/src/tracer.hpp" "$cadical_prefix/include/"
        install -m 644 "$cadical_source/build/libcadical.a" "$cadical_prefix/lib/"
        printf '%s\n' "$cadical_build_config" > "$cadical_prefix/.yasmv-build-config"
    else
        printf '%s\n' 'Using the cached CaDiCaL release dependency.'
    fi
fi

# extract microcode (do it only once)
if ! [ -f microcode/u-ge-26.json ]; then
   printf 'Extracting microcode ... '
   tar xfj microcode.tar.bz2
   printf 'done.\n'
fi

# generate configure script
autoreconf -vif

# User arguments come last so core-only builds, prefixes, and flags can override
# these defaults. Raw configure remains available for fully manual builds.
./configure --prefix=/usr/local --enable-llvm2smv \
    --with-cadical-prefix="$cadical_prefix" \
    CC="$CC" CXX="$CXX" CFLAGS="-O2" CXXFLAGS="$SETTINGS" "$@"

setup_make
