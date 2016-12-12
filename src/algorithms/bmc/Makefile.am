AM_CPPFLAGS=@AM_CPPFLAGS@ -I$(top_srcdir)/src																	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd -I$(top_srcdir)/src/dd/cudd-2.5.0/mtr	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st -I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CXXFLAGS=@AM_CXXFLAGS@
PKG_HH = bmc.hh typedefs.hh witness.hh
PKG_CC = bmc.cc forward.cc backward.cc witness.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libbmc.la
libbmc_la_SOURCES = $(PKG_CC)
