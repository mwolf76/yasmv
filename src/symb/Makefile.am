AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS =

AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = symbol.hh resolver.hh
PKG_CC = classes.cc iter.cc exceptions.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libsymb.la
libsymb_la_SOURCES = $(PKG_SOURCES)
