AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = grammars

INCLUDES = \
	-I$(top_srcdir)/src/ 				\
	-I$(top_srcdir)/src/expr 			\
	-I$(top_srcdir)/src/model 			\
	-I$(top_srcdir)/src/parser/grammars		\
	-I$(top_srcdir)/src/3rdparty/ezlogger

PKG_HH = grammars/smvLexer.h grammars/smvParser.h
PKG_CC = grammars/smvLexer.cc grammars/smvParser.cc

grammars/smvLexer.c grammars/smvParser.c: grammars/smv.g
	@echo "compiling ANTLR grammar... (this may take a while)"
	@java -cp /opt/jars/antlr-3.4-complete-no-antlrv2.jar org.antlr.Tool grammars/smv.g

grammars/smvLexer.cc: grammars/smvLexer.c
	@cp grammars/smvLexer.c grammars/smvLexer.cc

grammars/smvParser.cc: grammars/smvParser.c
	@cp grammars/smvParser.c grammars/smvParser.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libparser.la
libparser_la_SOURCES = $(PKG_SOURCES)
