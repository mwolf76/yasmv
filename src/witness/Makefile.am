AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = out

AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src																\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd -I$(top_srcdir)/src/dd/cudd-2.5.0/mtr	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st -I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_CC = witness.cc witness_mgr.cc evaluator.cc internals.cc exceptions.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libwitness.la
libwitness_la_SOURCES = $(PKG_CC)
