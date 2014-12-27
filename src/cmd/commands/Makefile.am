AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src/			\
-I$(top_srcdir)/src/dd -I$(top_srcdir)/src/enc				\
-I$(top_srcdir)/src/expr -I$(top_srcdir)/src/expr/walker		\
-I$(top_srcdir)/src/type -I$(top_srcdir)/src/symb			\
-I$(top_srcdir)/src/cmd -I$(top_srcdir)/src/micro			\
-I$(top_srcdir)/src/model -I$(top_srcdir)/src/sat			\
-I$(top_srcdir)/src/algorithms -I$(top_srcdir)/src/witness		\
-I$(top_srcdir)/src/utils -I$(top_srcdir)/src/sat/core			\
-I$(top_srcdir)/src/sat/mtl -I$(top_srcdir)/src/sat/proof		\
-I$(top_srcdir)/src/sat/utils -I$(top_srcdir)/src/parser/grammars	\
-I$(top_srcdir)/src/3rdparty/ezlogger					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = commands.hh
PKG_CC = commands.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libcommands.la
libcommands_la_SOURCES = $(PKG_SOURCES)
