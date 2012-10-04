INCLUDES = -I$(top_srcdir)/src -I$(top_srcdir)/src/expr -I$(top_srcdir)/src/3rdparty/ezlogger

AM_CPPFLAGS = @AM_CPPFLAGS@
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_SOURCES = test_expr.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libexpr_tests.la
libexpr_tests_la_SOURCES = $(PKG_SOURCES)
