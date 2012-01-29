# -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.
AC_PREREQ(2.60)

AC_INIT([gnusmv], [0.0.1], [marco.pensallorto@gmail.com])

# where to look for install.sh and other helpers
AC_CONFIG_AUX_DIR([helpers])
AC_CONFIG_MACRO_DIR([m4])
AM_CONFIG_HEADER([config.h])

# AM_INIT_AUTOMAKE([1.9 tar-ustar no-define])
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

dnl First look for Boost, maybe for a specific minimum version:
BOOST_REQUIRE([1.34])

dnl Then look for specific Boost libraries you need:
BOOST_REGEX

AC_DEFINE_UNQUOTED(PACKAGE_BUILD_DATE, "`date -u`", Build date)

# Library informations
AC_DEFINE_UNQUOTED(LIBRARY_NAME, "gnusmv", Library Name)
AC_DEFINE_UNQUOTED(LIBRARY_VERSION, "0.0.1", Library Version)
AC_DEFINE_UNQUOTED(LIBRARY_BUILD_DATE, "`date -u`", Library build date)
AC_DEFINE_UNQUOTED(LIBRARY_WEBSITE, "https://github.com/mwolf76", Library Website)
AC_DEFINE_UNQUOTED(LIBRARY_EMAIL, "marco.pensallorto@gmail.com", Library Email)
AC_DEFINE_UNQUOTED(LIBRARY_BUGREPORT, "Please report bugs to <marco.pensallorto@gmail.com>", Library bug message)

oldcflags=$CFLAGS
oldcxxflags=$CXXFLAGS
CFLAGS="-Wall -Wstrict-prototypes $excflags$oldcflags"
CXXFLAGS="-Wall $excflags$oldcflags"

if test "x$ac_cv_prog_CPP" != "x"; then
AC_DEFINE(HAVE_CPP, 1, Have preprocessor)
AC_DEFINE_UNQUOTED(PROG_CPP, "$ac_cv_prog_CPP -x c", Preprocessor call string)
else
AC_DEFINE(HAVE_CPP, 0, Have preprocessor)
fi

# Portability issues
AC_CHECK_SIZEOF([void *])
AC_CHECK_SIZEOF([int])
AC_CHECK_SIZEOF([long])
AC_CHECK_SIZEOF([long long])

# Checks for libraries.
AC_CHECK_LIB([m], [exp])

# AM_CONDITIONAL(HAVE_LIBEXPAT, test "x$ac_have_expat" = "xyes")
# AC_SUBST(HAVE_LIBEXPAT)

# Checks for header files.
dnl AC_HEADER_DIRENT
dnl AC_HEADER_STDC
dnl AC_CHECK_HEADERS([float.h limits.h memory.h stddef.h stdlib.h string.h \
dnl   sys/ioctl.h sys/param.h sys/time.h sys/resource.h unistd.h signal.h sys/signal.h \
dnl   errno.h regex.h inttypes.h])

dnl # This is for malloc:
dnl AC_CHECK_HEADER(sys/types.h)
dnl AC_CHECK_HEADER(malloc.h,
dnl 	[ AC_DEFINE(HAVE_MALLOC_H, 1, Defined to 1 if the system provides malloc.h)],
dnl 	[ AC_CHECK_HEADER(sys/malloc.h,
dnl 	    [AC_DEFINE(HAVE_SYS_MALLOC_H, 1, Defined to 1 if the system provides sys/malloc.h)],
dnl 	    [],
dnl 	    [
dnl 	      #if HAVE_SYS_TYPES_H
dnl 	      # include <sys/types.h>
dnl 	      #endif
dnl 	    ]
dnl 	    )],
dnl 	[
dnl 	 #if HAVE_SYS_TYPES_H
dnl 	 # include <sys/types.h>
dnl 	 #endif
dnl 	])


# Checks for typedefs, structures, and compiler characteristics.
AC_C_CONST
AC_HEADER_STDBOOL
AC_C_INLINE
AC_TYPE_SIZE_T

# Checks for library functions.
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

AC_CONFIG_FILES([Makefile
		 src/Makefile
		 src/expr/Makefile
                 src/expr/printers/Makefile
                 src/expr/validators/Makefile
                 src/model/Makefile
                 src/parser/Makefile
                 src/parser/grammars/Makefile
                 doc/Makefile
		 gnusmv.pc])

AC_OUTPUT
