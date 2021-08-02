AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = analyzer type_checker

AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = exceptions.hh model.hh model_mgr.hh model_resolver.hh	\
module.hh printers.hh typedefs.hh

PKG_CC = exceptions.cc model.cc module.cc model_mgr.cc	\
model_resolver.cc symb_iter.cc helpers.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libmodel.la
libmodel_la_SOURCES = $(PKG_HH) $(PKG_CC)
