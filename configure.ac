# -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.
AC_PREREQ(2.60)

AC_INIT([yasmv], [0.0.6], [marco.pensallorto@gmail.com])

# where to look for install.sh and other helpers
AC_CONFIG_AUX_DIR([helpers])
AC_CONFIG_MACRO_DIR([m4])
AM_CONFIG_HEADER([config.h])

AM_INIT_AUTOMAKE

AC_CANONICAL_HOST

# Checks for programs.
AC_PROG_INSTALL
AC_PROG_LN_S
AC_PROG_MAKE_SET
AC_PROG_LIBTOOL
AC_PROG_CC
AM_PROG_CC_C_O
AC_PROG_CPP
AC_PROG_CXX
AC_PROG_CXXCPP

# (optional) Doxygen
AC_CHECK_PROGS([DOXYGEN], [doxygen])
if test -z "$DOXYGEN";
   then AC_MSG_WARN([Doxygen not found - continuing without Doxygen support])
fi

AC_DEFINE_UNQUOTED(PACKAGE_BUILD_DATE, "`date -u`", Build date)

# Program informations
AC_DEFINE_UNQUOTED(PROGRAM_NAME, "yasmv", Program Name)
AC_DEFINE_UNQUOTED(PROGRAM_VERSION, "0.0.6", Program Version)
AC_DEFINE_UNQUOTED(PROGRAM_BUILD_DATE, "`date -u`", Program build date)
AC_DEFINE_UNQUOTED(PROGRAM_WEBSITE, "https://github.com/mwolf76", Program Website)
AC_DEFINE_UNQUOTED(PROGRAM_EMAIL, "marco.pensallorto@gmail.com", Program Email)
AC_DEFINE_UNQUOTED(PROGRAM_BUGREPORT, "Please report bugs to <marco.pensallorto@gmail.com>", Program bug message)

if test "x$ac_cv_prog_CPP" != "x"; then
AC_DEFINE(HAVE_CPP, 1, Have preprocessor)
AC_DEFINE_UNQUOTED(PROG_CPP, "$ac_cv_prog_CPP -x c", Preprocessor call string)
else
AC_DEFINE(HAVE_CPP, 0, Have preprocessor)
fi

# Portability issues
AC_CHECK_SIZEOF([void *])
SIZEOF_VOID_P=$ac_cv_sizeof_void_p
AC_SUBST(SIZEOF_VOID_P)

AC_CHECK_SIZEOF([int])
SIZEOF_INT=$ac_cv_sizeof_int
AC_SUBST(SIZEOF_INT)

AC_CHECK_SIZEOF([long])
SIZEOF_LONG=$ac_cv_sizeof_long
AC_SUBST(SIZEOF_LONG)

# Checks for libraries.
AC_CHECK_LIB([m], [exp])
AX_CHECK_ZLIB()

AM_CONDITIONAL([HAVE_DOXYGEN],
[test -n "$DOXYGEN"])AM_COND_IF([HAVE_DOXYGEN], [AC_CONFIG_FILES([doc/Doxyfile])])

# Checks for header files.
AC_HEADER_DIRENT
AC_HEADER_STDC
AC_CHECK_HEADERS([float.h limits.h memory.h stddef.h stdlib.h string.h \
  sys/ioctl.h sys/param.h sys/time.h sys/resource.h unistd.h signal.h sys/signal.h \
  errno.h regex.h inttypes.h])

# This is for malloc:
AC_CHECK_HEADER(sys/types.h)
AC_CHECK_HEADER(malloc.h,
        [ AC_DEFINE(HAVE_MALLOC_H, 1, Defined to 1 if the system provides malloc.h)],
        [ AC_CHECK_HEADER(sys/malloc.h,
            [AC_DEFINE(HAVE_SYS_MALLOC_H, 1, Defined to 1 if the system provides sys/malloc.h)],
            [],
            [
              #if HAVE_SYS_TYPES_H
              # include <sys/types.h>
              #endif
            ]
            )],
        [
         #if HAVE_SYS_TYPES_H
         # include <sys/types.h>
         #endif
        ])

# libjsoncpp
AC_LIBJSONCPP

# Yaml support
AC_LIBYAMLCPP

# ANTLR3 checks
AC_ANTLR3

# minisat checks
AC_MINISAT

# readline check
AX_LIB_READLINE

# Checks for typedefs, structures, and compiler characteristics.
AC_C_CONST
AC_HEADER_STDBOOL
AC_C_INLINE
AC_TYPE_SIZE_T

# Checks for program functions.
AC_FUNC_CLOSEDIR_VOID
AC_PROG_GCC_TRADITIONAL
AC_FUNC_MALLOC
AC_FUNC_REALLOC
AC_FUNC_SETVBUF_REVERSED
AC_TYPE_SIGNAL
AC_FUNC_STAT
AC_FUNC_STRTOD
AC_FUNC_VPRINTF
AC_CHECK_FUNCS([floor memmove memset pow strcasecmp strchr \
                strrchr strstr strtol, random srandom getpid \
                mkstemp mktemp tmpnam getenv setvbuf system popen isatty])

dnl First look for Boost
BOOST_REQUIRE([1.48])

dnl Then look for specific Boost libraries you need:
BOOST_FILESYSTEM
BOOST_PROGRAM_OPTIONS
BOOST_TEST
BOOST_THREADS
BOOST_CHRONO

AM_CPPFLAGS="$BOOST_CPPFLAGS $ANTLR_CPPFLAGS -DYASMV_MICROCODE=$datadir/$PACKAGE"
AC_SUBST(AM_CPPFLAGS)

AM_CFLAGS="-Wall -Wstrict-prototypes"
AC_SUBST(AM_CFLAGS)

AM_CXXFLAGS="-Wall"
AC_SUBST(AM_CXXFLAGS)

AC_CONFIG_FILES([Makefile
                 src/Makefile
                 src/3rdparty/Makefile
                 src/3rdparty/ezlogger/Makefile
                 src/cmd/Makefile
                 src/cmd/commands/Makefile
                 src/common/Makefile
                 src/dd/Makefile
                 src/enc/Makefile
                 src/env/Makefile
                 src/expr/Makefile
                 src/expr/printer/Makefile
                 src/expr/walker/Makefile
                 src/algorithms/Makefile
                 src/algorithms/bmc/Makefile
                 src/algorithms/fsm/Makefile
                 src/algorithms/ltl/Makefile
                 src/algorithms/sim/Makefile
                 src/symb/Makefile
                 src/model/Makefile
                 src/model/analyzer/Makefile
                 src/model/compiler/Makefile
                 src/model/type_checker/Makefile
                 src/model/preprocessor/Makefile
                 src/opts/Makefile
                 src/parser/Makefile
                 src/parser/grammars/Makefile
                 src/sat/Makefile
                 src/type/Makefile
                 src/utils/Makefile
                 src/witness/Makefile
                 src/witness/out/Makefile
                 doc/Makefile
                 yasmv.pc])

AC_OUTPUT
