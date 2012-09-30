ACLOCAL_AMFLAGS = -I m4
SUBDIRS = src doc

PACKAGE = $(PACKAGE_NAME)
VERSION = $(PACKAGE_VERSION)

READMES = LGPL-2.1 NEWS README

INCLUDES = -I$(top_srcdir)/src -I$(top_srcdir)/src/expr			\
-I$(top_srcdir)/src/expr/printers -I$(top_srcdir)/src/expr/validators	\
-I$(top_srcdir)/src/model -I$(top_srcdir)/src/cmd			\
-I$(top_srcdir)/src/3rdparty/ezlogger					\
-I$(top_srcdir)/src/parser/grammars -I$(top_srcdir)/src/mc		\
-I$(top_srcdir)/src/3rdparty/ezlogger -I$(top_srcdir)/src/sat/core	\
-I$(top_srcdir)/src/sat -I$(top_srcdir)/src/sat/mtl			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/epd					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

# Programs to be built
bin_PROGRAMS = smv

smv_SOURCES = src/opts.cc src/main.cc
smv_LDADD = $(top_builddir)/src/expr/printers/libexpr_printers.la	\
	$(top_builddir)/src/expr/validators/libexpr_validators.la	\
	$(top_builddir)/src/parser/libparser.la				\
	$(top_builddir)/src/cmd/libcommand.la				\
	$(top_builddir)/src/mc/libmc.la \
	$(top_builddir)/src/expr/compilers/libexpr_compilers.la \
	$(top_builddir)/src/model/libmodel.la				\
	$(top_builddir)/src/expr/libexpr.la				\
	$(top_builddir)/src/dd/libcudd.la				\
	$(top_builddir)/src/sat/libminisat.la -lantlr3c			\
	$(BOOST_REGEX_LIBS) $(BOOST_PROGRAM_OPTIONS_LIBS)

smv_LDFLAGS = $(BOOST_REGEX_LDFLAGS)

pkgconfdir = $(libdir)/pkgconfig
pkgconf_DATA = gnusmv.pc