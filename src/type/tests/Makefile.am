INCLUDES = -I$(top_srcdir)/src -I$(top_srcdir)/src/expr		\
-I$(top_srcdir)/src/type -I$(top_srcdir)/src/expr/walkers	\
-I$(top_srcdir)/src/3rdparty/ezlogger

AM_CPPFLAGS = @AM_CPPFLAGS@
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_SOURCES = test_type.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libtype_tests.la
libtype_tests_la_SOURCES = $(PKG_SOURCES)
