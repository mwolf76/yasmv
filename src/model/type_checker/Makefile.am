AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

PKG_HH = type_checker.hh
PKG_CC = type_checker.cc internals.cc

# -------------------------------------------------------
noinst_LTLIBRARIES = libtype_checker.la
libtype_checker_la_SOURCES = $(PKG_HH) $(PKG_CC)
