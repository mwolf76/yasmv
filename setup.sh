#!/bin/sh
#
# Copyright (C) 2016 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
#
# This library is free software; you can redistribute it and/or
# modify it under the terms of the GNU Lesser General Public
# License as published by the Free Software Foundation; either
# version 2.1 of the License, or (at your option) any later version.
#
# This library is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#  Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public
# License along with this library; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
#

# set to 1 to enable distcc compilation
USE_DISTCC=0

# set to 1 to make a debugger-friendly build
USE_DEBUGGER=1

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

COMMON_OPTIONS="-fPIC"

if [ $USE_DEBUGGER -eq 1 ];
then
    # compilation options for debugging, all + extra warnings enabled. Any warning is fatal.
    OPTIONS="-g -O0"
else
    # compilation options for debugging, all + extra warnings enabled. Any warning is fatal.
    OPTIONS="-O2"
fi

if [ $USE_STRICT -eq 1 ];
then
    # compilation options for debugging, all + extra warnings enabled. Any warning is fatal.
    FLAGS="-Wall -Werror"
else
    # compilation options for debugging, all + extra warnings enabled. Any warning is fatal.
    FLAGS=""
fi

SETTINGS="$DEFINES $COMMON_OPTIONS $OPTIONS $FLAGS"

# invoking configure script with above settings
./configure CC="$CC" CXX="$CXX" CFLAGS="-O2" CXXFLAGS="$SETTINGS"
