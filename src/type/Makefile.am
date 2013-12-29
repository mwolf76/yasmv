AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS =

INCLUDES = -I$(top_srcdir)/src 				\
-I$(top_srcdir)/src/expr				\
-I$(top_srcdir)/src/type 				\
-I$(top_srcdir)/src/symb 				\
-I$(top_srcdir)/src/dd					\
-I$(top_srcdir)/src/3rdparty/ezlogger			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CPPFLAGS = @AM_CPPFLAGS@
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = type.hh type_mgr.hh type_resolver.hh

PKG_CC = type.cc type_mgr.cc type_resolver.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libtype.la
libtype_la_SOURCES = $(PKG_SOURCES)
