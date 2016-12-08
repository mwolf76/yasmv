AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = analyzer compiler type_checker preprocessor

AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src																\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd -I$(top_srcdir)/src/dd/cudd-2.5.0/mtr	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st -I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_SOURCES = exceptions.cc classes.cc symb_iter.cc model_mgr.cc	\
model_resolver.cc symb_iter.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libmodel.la
libmodel_la_SOURCES = $(PKG_SOURCES)
