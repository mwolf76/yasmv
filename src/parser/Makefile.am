SUBDIRS = grammars
AUTOMAKE_OPTIONS = subdir-objects

INCLUDES = -I$(top_srcdir)/src/ -I$(top_srcdir)/src/expr -I$(top_srcdir)/src/model -I$(top_srcdir)/src/parser/grammars

PKG_HH = grammars/smvLexer.h
PKG_CC = grammars/smvLexer.c

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libparser.la
libparser_la_SOURCES = $(PKG_SOURCES)
