AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = walkers tests
INCLUDES = -I$(top_srcdir)/src -I$(top_srcdir)/src/expr			\
-I$(top_srcdir)/src/expr/walkers -I$(top_srcdir)/src/3rdparty/ezlogger

AM_CPPFLAGS = @AM_CPPFLAGS@
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = expr.hh pool.hh expr_mgr.hh expr_printer.hh
PKG_CC = expr.cc pool.cc expr_mgr.cc expr_printer.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libexpr.la
libexpr_la_SOURCES = $(PKG_SOURCES)
