AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = grammars

AM_CPPFLAGS = @AM_CPPFLAGS@
AM_CXXFLAGS = -Wno-unused-variable -Wno-unused-function -DANTLR3_INLINE_INPUT_8BIT

INCLUDES = -I$(top_srcdir)/src/ -I$(top_srcdir)/src/dd			\
-I$(top_srcdir)/src/enc -I$(top_srcdir)/src/expr			\
-I$(top_srcdir)/src/expr/walkers -I$(top_srcdir)/src/type		\
-I$(top_srcdir)/src/cmd -I$(top_srcdir)/src/model			\
-I$(top_srcdir)/src/sat -I$(top_srcdir)/src/mc				\
-I$(top_srcdir)/src/utils -I$(top_srcdir)/src/witness			\
-I$(top_srcdir)/src/sat/core -I$(top_srcdir)/src/sat/mtl		\
-I$(top_srcdir)/src/sat/proof -I$(top_srcdir)/src/sat/utils		\
-I$(top_srcdir)/src/grammars -I$(top_srcdir)/src/3rdparty/ezlogger	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/epd					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

PKG_HH = grammars/smvLexer.h grammars/smvParser.h
PKG_CC = grammars/smvLexer.cc grammars/smvParser.cc

grammars/smvLexer.c grammars/smvParser.c: grammars/smv.g
	@echo "compiling ANTLR grammar... (this may take a while)"
	@antlr3 grammars/smv.g

grammars/smvLexer.cc: grammars/smvLexer.c
	@cp grammars/smvLexer.c grammars/smvLexer.cc

grammars/smvParser.cc: grammars/smvParser.c
	@cp grammars/smvParser.c grammars/smvParser.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libparser.la
libparser_la_SOURCES = $(PKG_SOURCES)
