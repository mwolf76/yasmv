# LLVM autoconf macros
# AC_LLVM: Check for LLVM installation and set flags

AC_DEFUN([AC_LLVM],
[
  AC_ARG_ENABLE([llvm2smv],
    [AS_HELP_STRING([--enable-llvm2smv], [build LLVM to SMV translator (default: yes)])],
    [enable_llvm2smv="$enableval"],
    [enable_llvm2smv="yes"])

  AC_ARG_WITH([llvm-config],
    [AS_HELP_STRING([--with-llvm-config=PATH], [path to llvm-config executable])],
    [LLVM_CONFIG="$withval"],
    [AC_PATH_PROGS([LLVM_CONFIG],
                   [llvm-config llvm-config-15 llvm-config-14 llvm-config-13 llvm-config-12 llvm-config-11 llvm-config-10],
                   [no])])

  if test "$enable_llvm2smv" = "yes"; then
    if test "$LLVM_CONFIG" = "no"; then
      AC_MSG_ERROR([LLVM not found. Please install LLVM development packages, specify --with-llvm-config, or use --disable-llvm2smv])
    fi
  fi

  if test "$enable_llvm2smv" = "yes"; then
    # Check LLVM version
    LLVM_VERSION=`$LLVM_CONFIG --version`
    AC_MSG_CHECKING([LLVM version])
    AC_MSG_RESULT([$LLVM_VERSION])

    # Set LLVM flags
    LLVM_CPPFLAGS=`$LLVM_CONFIG --cppflags | sed 's/-std=c++[[0-9]][[0-9]]//g'`
    LLVM_LDFLAGS=`$LLVM_CONFIG --ldflags`
    LLVM_LIBS=`$LLVM_CONFIG --libs core irreader support passes analysis bitwriter transformutils`

    # Check for clang
    AC_PATH_PROG([CLANG], [clang], [no])
    if test "$CLANG" = "no"; then
      AC_MSG_WARN([clang not found. C to LLVM IR compilation will not work.])
    fi

    # Define preprocessor macros
    AC_DEFINE([HAVE_LLVM], [1], [Define if LLVM is available])
  else
    AC_MSG_NOTICE([LLVM2SMV support disabled])
    LLVM_CONFIG=""
    LLVM_CPPFLAGS=""
    LLVM_LDFLAGS=""
    LLVM_LIBS=""
    CLANG="no"
  fi

  # Export variables
  AC_SUBST([LLVM_CONFIG])
  AC_SUBST([LLVM_CPPFLAGS])
  AC_SUBST([LLVM_LDFLAGS])
  AC_SUBST([LLVM_LIBS])
  AC_SUBST([CLANG])

  # Conditional compilation
  AM_CONDITIONAL([ENABLE_LLVM2SMV], [test "$enable_llvm2smv" = "yes"])
])
