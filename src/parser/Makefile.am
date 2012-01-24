AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = grammars

INCLUDES = -I$(top_srcdir)/src/ -I$(top_srcdir)/src/expr -I$(top_srcdir)/src/model -I$(top_srcdir)/src/parser/grammars

PKG_HH = grammars/smvLexer.h grammars/smvParser.h
PKG_CC = grammars/smvLexer.c grammars/smvParser.c

grammars/smvLexer.c grammars/smvParser.c: grammars/smv.g
	@echo "compiling ANTLR grammar... (this may take a while)"
	@java -cp /opt/jars/antlr-3.4-complete-no-antlrv2.jar org.antlr.Tool grammars/smv.g

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libparser.la
libparser_la_SOURCES = $(PKG_SOURCES)
