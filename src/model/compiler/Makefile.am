AM_CPPFLAGS = -I$(top_srcdir)/src/ -I$(top_srcdir)/src/dd	\
-I$(top_srcdir)/src/enc -I$(top_srcdir)/src/expr		\
-I$(top_srcdir)/src/type -I$(top_srcdir)/src/symb		\
-I$(top_srcdir)/src/expr/walker -I$(top_srcdir)/src/micro	\
-I$(top_srcdir)/src/model -I$(top_srcdir)/src/model/compiler	\
-I$(top_srcdir)/src/3rdparty/ezlogger -I$(top_srcdir)/src/sat	\
-I$(top_srcdir)/src/sat/core -I$(top_srcdir)/src/sat/mtl	\
-I$(top_srcdir)/src/sat/proof -I$(top_srcdir)/src/sat/utils	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

PKG_HH = compiler.hh exceptions.hh unit.hh

PKG_CC = compiler.cc algebra.cc boolean.cc enumerative.cc array.cc	\
internals.cc leaves.cc analysis.cc exceptions.cc walker.cc unit.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libcompiler.la
libcompiler_la_SOURCES = $(PKG_HH) $(PKG_CC)
