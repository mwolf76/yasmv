# LLVM 18 is the explicitly tested llvm2smv baseline. Core-only builds do not
# discover or invoke any LLVM tools.
AC_DEFUN([AC_LLVM],
[
  AC_ARG_ENABLE([llvm2smv],
    [AS_HELP_STRING([--enable-llvm2smv], [build LLVM 18 analysis frontend (default: yes)])],
    [enable_llvm2smv="$enableval"], [enable_llvm2smv=yes])
  AS_CASE([$enable_llvm2smv], [yes|no], [],
    [AC_MSG_ERROR([--enable-llvm2smv expects yes or no])])
  AC_ARG_WITH([llvm-config],
    [AS_HELP_STRING([--with-llvm-config=PATH], [LLVM 18 llvm-config executable])],
    [LLVM_CONFIG="$withval"])
  AC_ARG_VAR([CLANG], [Clang matching the selected llvm-config])
  AC_ARG_VAR([LLVM_OPT], [opt matching the selected llvm-config])
  AC_ARG_VAR([LLVM_LINK], [llvm-link matching the selected llvm-config])

  AS_IF([test "x$enable_llvm2smv" = xyes], [
    AS_IF([test -z "$LLVM_CONFIG"],
      [AC_PATH_PROGS([LLVM_CONFIG], [llvm-config-18 llvm-config], [no])])
    AS_IF([test "x$LLVM_CONFIG" = xno],
      [AC_MSG_ERROR([LLVM 18 is required; install llvm-18-dev and clang-18, use --with-llvm-config, or --disable-llvm2smv])])
    LLVM_VERSION=`"$LLVM_CONFIG" --version` || AC_MSG_ERROR([cannot execute llvm-config])
    AS_CASE([$LLVM_VERSION], [18.*], [],
      [AC_MSG_ERROR([llvm2smv requires LLVM 18; selected version is $LLVM_VERSION])])
    AC_MSG_NOTICE([llvm2smv toolchain: LLVM $LLVM_VERSION])
    LLVM_BINDIR=`"$LLVM_CONFIG" --bindir` || AC_MSG_ERROR([cannot locate LLVM tools])
    AS_IF([test -z "$CLANG"], [CLANG="$LLVM_BINDIR/clang"])
    AS_IF([test -z "$LLVM_OPT"], [LLVM_OPT="$LLVM_BINDIR/opt"])
    AS_IF([test -z "$LLVM_LINK"], [LLVM_LINK="$LLVM_BINDIR/llvm-link"])
    for llvm_tool in "$CLANG" "$LLVM_OPT" "$LLVM_LINK"; do
      AC_MSG_CHECKING([version of $llvm_tool])
      llvm_tool_output=`"$llvm_tool" --version 2>&1` || AC_MSG_ERROR([cannot execute $llvm_tool])
      llvm_tool_version=`echo "$llvm_tool_output" | sed -n 's/.*version \([[0-9]][[0-9.]]*\).*/\1/p' | head -n 1`
      AC_MSG_RESULT([$llvm_tool_version])
      AS_IF([test "x$llvm_tool_version" != "x$LLVM_VERSION"],
        [AC_MSG_ERROR([$llvm_tool must match LLVM $LLVM_VERSION; found $llvm_tool_version])])
    done
    LLVM_CPPFLAGS=`"$LLVM_CONFIG" --cppflags` || AC_MSG_ERROR([cannot read LLVM compiler flags])
    LLVM_LDFLAGS=`"$LLVM_CONFIG" --ldflags` || AC_MSG_ERROR([cannot read LLVM linker flags])
    LLVM_LIBS=`"$LLVM_CONFIG" --libs core irreader support analysis transformutils targetparser --system-libs` || AC_MSG_ERROR([cannot read LLVM libraries])
    AC_DEFINE([HAVE_LLVM], [1], [Define if LLVM is available])
  ], [
    AC_MSG_NOTICE([LLVM2SMV support disabled])
    LLVM_CONFIG=""
    LLVM_VERSION=""
    LLVM_CPPFLAGS=""
    LLVM_LDFLAGS=""
    LLVM_LIBS=""
    CLANG="no"
    LLVM_OPT="no"
    LLVM_LINK="no"
  ])
  AC_SUBST([LLVM_CONFIG])
  AC_SUBST([LLVM_VERSION])
  AC_SUBST([LLVM_CPPFLAGS])
  AC_SUBST([LLVM_LDFLAGS])
  AC_SUBST([LLVM_LIBS])
  AC_SUBST([CLANG])
  AC_SUBST([LLVM_OPT])
  AC_SUBST([LLVM_LINK])
  AM_CONDITIONAL([ENABLE_LLVM2SMV], [test "x$enable_llvm2smv" = xyes])
])
