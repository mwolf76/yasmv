AM_CPPFLAGS = @AM_CPPFLAGS@ -I/usr/local/include -I$(top_srcdir)/src	\
-I$(top_srcdir)/src/sat -I$(top_srcdir)/src/dd/cudd-2.5.0/cudd		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CFLAGS = @AM_CFLAGS@
AM_CXXFLAGS = -Wno-unused-variable -Wno-unused-function

PKG_HH = satdefs.hh sat.hh
PKG_CC = cnf_registry.cc time_mapper.cc cnf_nocut.cc cnf_singlecut.cc	\
cnf_inject.cc solver.cc logger.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libsat.la
libsat_la_SOURCES = $(PKG_SOURCES)
