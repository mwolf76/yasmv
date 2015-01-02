AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src/	\
-I$(top_srcdir)/src/expr -I$(top_srcdir)/src/dd		\
-I$(top_srcdir)/src/enc -I$(top_srcdir)/src/expr/walker	\
-I$(top_srcdir)/src/type -I$(top_srcdir)/src/symb	\
-I$(top_srcdir)/src/mc -I$(top_srcdir)/src/sat		\
-I$(top_srcdir)/src/3rdparty/ezlogger			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = micro.hh micro_loader.hh micro_mgr.hh
PKG_CC = micro.cc micro_loader.cc micro_mgr.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libmicro.la
libmicro_la_SOURCES = $(PKG_SOURCES)
