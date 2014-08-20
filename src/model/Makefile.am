AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = compiler

AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src/		\
-I$(top_srcdir)/src/expr -I$(top_srcdir)/src/dd			\
-I$(top_srcdir)/src/enc -I$(top_srcdir)/src/expr/walker		\
-I$(top_srcdir)/src/type -I$(top_srcdir)/src/symb		\
-I$(top_srcdir)/src/mc -I$(top_srcdir)/src/3rdparty/ezlogger	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = model.hh model_mgr.hh preprocessor.hh inferrer.hh model_resolver.hh

PKG_CC = model.cc model_mgr.cc preprocessor.cc inferrer.cc model_resolver.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libmodel.la
libmodel_la_SOURCES = $(PKG_SOURCES)
