AM_CPPFLAGS = @AM_CPPFLAGS@ -I/usr/local/include -I$(top_srcdir)/src					\
-I$(top_srcdir)/src/sat -I$(top_srcdir)/src/dd/cudd-2.5.0/cudd								\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr -I$(top_srcdir)/src/dd/cudd-2.5.0/st		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util -I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CFLAGS = @AM_CFLAGS@
AM_CXXFLAGS = -Wno-unused-variable -Wno-unused-function

PKG_HH = engine.hh engine_mgr.hh exceptions.hh inlining.hh logging.hh sat.hh	\
typedefs.hh

PKG_CC = cnf_nocut.cc cnf_singlecut.cc cnf_auxcut.cc engine.cc	\
engine_mgr.cc exceptions.cc inlining.cc logging.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libsat.la
libsat_la_SOURCES = $(PKG_HH) $(PKG_CC)
