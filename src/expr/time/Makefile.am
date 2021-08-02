AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = analyzer expander

AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = timed_expr.hh
PKG_CC = timed_expr.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libexpr_time.la
libexpr_time_la_SOURCES = $(PKG_HH) $(PKG_CC)
