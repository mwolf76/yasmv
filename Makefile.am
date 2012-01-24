ACLOCAL_AMFLAGS = -I m4
SUBDIRS = src doc

PACKAGE = $(PACKAGE_NAME)
VERSION = $(PACKAGE_VERSION)

AM_CPPFLAGS = -DDATADIR=\"$(datadir)\" @CPPFLAGS@
READMES = LGPL-2.1 NEWS README

INCLUDES = 					\
	-I$(top_srcdir)/src 			\
	-I$(top_srcdir)/src/expr 		\
	-I$(top_srcdir)/src/model 		\
	-I$(top_srcdir)/src/3rdparty/ezlogger 	\
	-I$(top_srcdir)/src/parser/grammars

# Programs to be built
bin_PROGRAMS = smv

smv_SOURCES = src/main.cc
smv_LDADD = 						\
	$(top_builddir)/src/expr/libexpr.la 		\
	$(top_builddir)/src/model/libmodel.la 		\
	$(top_builddir)/src/parser/libparser.la   	\
	-lantlr3c

pkgconfdir = $(libdir)/pkgconfig
pkgconf_DATA = gnusmv.pc