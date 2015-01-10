AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = grammars

AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CXXFLAGS = -Wno-unused-variable -Wno-unused-function -Wno-unused-but-set-variable -DANTLR3_INLINE_INPUT_8BIT

PKG_HH = grammars/smvLexer.h grammars/smvParser.h
PKG_CC = grammars/smvLexer.cc grammars/smvParser.cc

grammars/.timestamp: grammars/smv.g
	@echo "compiling ANTLR grammar... (this may take a while)"
	@antlr3 grammars/smv.g
	@touch grammars/.timestamp

grammars/smvLexer.cc: grammars/.timestamp
	@cp grammars/smvLexer.c grammars/smvLexer.cc

grammars/smvParser.cc: grammars/.timestamp
	@cp grammars/smvParser.c grammars/smvParser.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libparser.la
libparser_la_SOURCES = $(PKG_SOURCES)
