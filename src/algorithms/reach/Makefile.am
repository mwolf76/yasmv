AM_CPPFLAGS=@AM_CPPFLAGS@ -I$(top_srcdir)/src	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CXXFLAGS=@AM_CXXFLAGS@

PKG_HH = reach.hh typedefs.hh witness.hh
PKG_CC = reach.cc forward.cc backward.cc fast_forward.cc fast_backward.cc witness.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libreach.la
libreach_la_SOURCES = $(PKG_HH) $(PKG_CC)
