# Locate and verify the pinned external static CaDiCaL build. No downloads.
AC_DEFUN([AC_CADICAL], [
  AC_ARG_WITH([cadical-prefix],
    [AS_HELP_STRING([--with-cadical-prefix=PATH],
      [CaDiCaL 3.0.1 prefix containing include/cadical.hpp and lib/libcadical.a (default /usr/local)])],
    [cadical_prefix="$withval"], [cadical_prefix="/usr/local"])
  AS_IF([test ! -d "$cadical_prefix"],
    [AC_MSG_ERROR([CaDiCaL prefix does not exist; see docs/CADICAL_BACKEND.md])])
  cadical_prefix=`cd "$cadical_prefix" && pwd`
  CADICAL_CPPFLAGS="-I$cadical_prefix/include"
  CADICAL_LIBS="$cadical_prefix/lib/libcadical.a"
  AS_IF([test ! -f "$CADICAL_LIBS"],
    [AC_MSG_ERROR([Pinned static libcadical.a not found; see docs/CADICAL_BACKEND.md])])
  cadical_save_CPPFLAGS="$CPPFLAGS"
  cadical_save_LIBS="$LIBS"
  CPPFLAGS="$CPPFLAGS $CADICAL_CPPFLAGS"
  LIBS="$CADICAL_LIBS $LIBS"
  AC_LANG_PUSH([C++])
  AC_MSG_CHECKING([for the pinned CaDiCaL version, revision, and incremental API])
  # Capture stdout before process startup: CaDiCaL caches terminal colour
  # support in global constructors, so freopen inside main is too late.
  cadical_api_ok=no
  {
  AC_RUN_IFELSE([AC_LANG_PROGRAM([[
#include <cadical.hpp>
#include <cstdio>
#include <cstring>
#include <climits>
struct Stop : CaDiCaL::Terminator { bool terminate() override { return false; } };
]], [[
    if (std::strcmp(CaDiCaL::Solver::version(), "3.0.1") ||
        std::strcmp(CaDiCaL::Solver::signature(), "cadical-3.0.1-c607304")) return 1;
    Stop stop;
    CaDiCaL::Solver solver;
    if (!solver.set("quiet", 1) || !solver.set("seed", 0)) return 2;
    solver.connect_terminator(&stop);
    int x = solver.declare_one_more_variable();
    solver.freeze(x);
    solver.add(x); solver.add(0);
    if (!solver.limit("conflicts", INT_MAX) || solver.solve() != 10) return 3;
    if (solver.val(x) != x || solver.get_statistic_value("propagations") < 0 ||
        solver.get_statistic_value("conflicts") < 0 ||
        solver.get_statistic_value("decisions") < 0) return 4;
    solver.assume(-x);
    if (solver.solve() != 20 || !solver.failed(-x)) return 5;
    if (solver.solve() != 10) return 6;
    solver.melt(x); solver.disconnect_terminator();
    CaDiCaL::Solver::build(stdout, "");
  ]])],
    [cadical_api_ok=yes],
    [cadical_api_ok=no],
    [AC_MSG_ERROR([Cross compilation requires a runnable pinned CaDiCaL validation; unsupported by this gate])])
  } >conftest.cadical-build
  cat conftest.cadical-build >&AS_MESSAGE_LOG_FD
  AS_IF([test "$cadical_api_ok" != yes],
    [AC_MSG_ERROR([CaDiCaL API/version check failed; see config.log and docs/CADICAL_BACKEND.md])])
  AS_IF([grep -F "Version 3.0.1 c60730422e758ef1cebe7aeddf2dda31c996bf04" conftest.cadical-build >/dev/null],
    [AC_MSG_RESULT([yes])],
    [AC_MSG_ERROR([CaDiCaL library does not report the required full build revision; see config.log])])
  AC_LANG_POP([C++])
  CPPFLAGS="$cadical_save_CPPFLAGS"
  LIBS="$cadical_save_LIBS"
  AC_DEFINE([CADICAL_BUILD_REVISION], ["c60730422e758ef1cebe7aeddf2dda31c996bf04"],
    [Verified revision reported by the linked CaDiCaL library])
  AC_SUBST([CADICAL_CPPFLAGS])
  AC_SUBST([CADICAL_LIBS])
])
