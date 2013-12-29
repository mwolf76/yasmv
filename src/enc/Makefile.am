AUTOMAKE_OPTIONS = subdir-objects

INCLUDES = -I$(top_srcdir)/src -I$(top_srcdir)/src/expr	\
-I$(top_srcdir)/src/type -I$(top_srcdir)/src/dd		\
-I$(top_srcdir)/src/3rdparty/ezlogger			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj


AM_CPPFLAGS = @AM_CPPFLAGS@
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = enc.hh enc_mgr.hh

PKG_CC = enc.cc enc_mgr.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libenc.la
libenc_la_SOURCES = $(PKG_SOURCES)
