AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS =

AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = classes.hh exceptions.hh helpers.hh printers.hh typedefs.hh	\
type.hh type_mgr.hh type_resolver.hh

PKG_CC = algebraic.cc array.cc classes.cc exceptions.cc instance.cc	\
monolithic.cc printers.cc type.cc type_mgr.cc type_resolver.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libtype.la
libtype_la_SOURCES = $(PKG_HH) $(PKG_CC)

