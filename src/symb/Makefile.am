AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS =

AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = classes.hh exceptions.hh proxy.hh resolver.hh symb_iter.hh	\
typedefs.hh

PKG_CC = classes.cc exceptions.cc symb_iter.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libsymb.la
libsymb_la_SOURCES = $(PKG_HH) $(PKG_CC)
