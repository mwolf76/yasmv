AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS =

AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = classes.hh exceptions.hh type.hh type_mgr.hh type_resolver.hh
PKG_CC = classes.cc printers.cc type_mgr.cc type_resolver.cc exceptions.cc	\
monolithic.cc algebraic.cc array.cc instance.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libtype.la
libtype_la_SOURCES = $(PKG_SOURCES)
