AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = walker printer

AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src			\
-I$(top_srcdir)/src/expr -I$(top_srcdir)/src/expr/walker	\
-I$(top_srcdir)/src/expr/printer				\
-I$(top_srcdir)/src/3rdparty/ezlogger
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = expr.hh pool.hh expr_mgr.hh
PKG_CC = expr.cc pool.cc expr_mgr.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libexpr.la
libexpr_la_SOURCES = $(PKG_SOURCES)
