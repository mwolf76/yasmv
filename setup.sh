#!/bin/sh

# a few useful standard defines
DEFINES="-D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -DPIC"

# compilation options for debugging, all + extra warnings enabled. Any warning is fatal.
OPTIONS="-g -O0 -fPIC -Wall -Werror"

ALLFLAGS="$DEFINES $OPTIONS"

# invoke configure script with above settings
./configure CFLAGS="-O2" CXXFLAGS="$ALLFLAGS"
