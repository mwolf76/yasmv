AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = out

AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = evaluator.hh exceptions.hh witness.hh witness_mgr.hh

PKG_CC = evaluator.cc exceptions.cc internals.cc witness.cc	\
witness_mgr.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libwitness.la
libwitness_la_SOURCES = $(PKG_HH) $(PKG_CC)
