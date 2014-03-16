ACLOCAL_AMFLAGS = -I m4
SUBDIRS = src doc

PACKAGE = $(PACKAGE_NAME)
VERSION = $(PACKAGE_VERSION)

READMES = LGPL-2.1 NEWS README

INCLUDES = -I$(top_srcdir)/src -I$(top_srcdir)/src/dd			\
-I$(top_srcdir)/src/enc -I$(top_srcdir)/src/expr			\
-I$(top_srcdir)/src/type -I$(top_srcdir)/src/symb			\
-I$(top_srcdir)/src/expr/walker -I$(top_srcdir)/src/expr/printer	\
-I$(top_srcdir)/src/model -I$(top_srcdir)/src/cmd			\
-I$(top_srcdir)/src/utils -I$(top_srcdir)/src/witness			\
-I$(top_srcdir)/src/3rdparty/ezlogger					\
-I$(top_srcdir)/src/parser/grammars -I$(top_srcdir)/src/algorithms	\
-I$(top_srcdir)/src/3rdparty/ezlogger -I$(top_srcdir)/src/sat/core	\
-I$(top_srcdir)/src/sat -I$(top_srcdir)/src/sat/mtl			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util					\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

# Overriding 'all' target raises make warnings. Peace.
all: config.h
	$(MAKE) $(AM_MAKEFLAGS) all-recursive
	@./tests --log_level=test_suite
	@echo "Done."

bin_PROGRAMS = yasmv tests

# tags target helper  (uses exuberant ctags)
tags:
	@ctags -Re $(top_srcdir)

yasmv_SOURCES = src/opts.cc src/main.cc src/parse.cc src/common.cc
yasmv_LDADD = $(top_builddir)/src/parser/libparser.la		\
	$(top_builddir)/src/cmd/libcommand.la			\
	$(top_builddir)/src/algorithms/bmc/libbmc.la		\
	$(top_builddir)/src/algorithms/sim/libsim.la		\
	$(top_builddir)/src/algorithms/libalgorithms.la		\
	$(top_builddir)/src/model/libmodel.la			\
	$(top_builddir)/src/model/compiler/libcompiler.la	\
	$(top_builddir)/src/expr/libexpr.la			\
	$(top_builddir)/src/expr/walker/libexpr_walker.la	\
	$(top_builddir)/src/expr/printer/libprinter.la		\
	$(top_builddir)/src/type/libtype.la			\
	$(top_builddir)/src/symb/libsymb.la			\
	$(top_builddir)/src/enc/libenc.la			\
	$(top_builddir)/src/utils/libutils.la			\
	$(top_builddir)/src/witness/libwitness.la		\
	$(top_builddir)/src/dd/libcudd.la			\
	$(top_builddir)/src/sat/minisat/libminisat.la		\
	$(top_builddir)/src/sat/libsat.la			\
	$(top_builddir)/src/dd/libcudd.la -lantlr3c		\
	$(BOOST_PROGRAM_OPTIONS_LIBS) $(BOOST_THREAD_LIBS)

tests_SOURCES = src/opts.cc s $(top_srcdir)/src/tests.cc src/parse.cc	\
	src/common.cc $(top_srcdir)/src/expr/tests/test_expr.cc		\
	$(top_srcdir)/src/parser/tests/test_parser.cc			\
	$(top_srcdir)/src/type/tests/test_type.cc			\
	$(top_srcdir)/src/dd/tests/test_dd.cc				\
	$(top_srcdir)/src/enc/tests/test_enc.cc				\
	$(top_srcdir)/src/model/tests/test_compiler.cc

tests_LDADD = $(top_builddir)/src/parser/libparser.la			\
	$(top_builddir)/src/cmd/libcommand.la				\
	$(top_builddir)/src/algorithms/bmc/libbmc.la			\
	$(top_builddir)/src/algorithms/sim/libsim.la			\
	$(top_builddir)/src/algorithms/libalgorithms.la			\
	$(top_builddir)/src/model/libmodel.la				\
	$(top_builddir)/src/model/compiler/libcompiler.la		\
	$(top_builddir)/src/expr/libexpr.la				\
	$(top_builddir)/src/expr/walker/libexpr_walker.la		\
	$(top_builddir)/src/expr/printer/libprinter.la			\
	$(top_builddir)/src/type/libtype.la				\
	$(top_builddir)/src/symb/libsymb.la				\
	$(top_builddir)/src/enc/libenc.la				\
	$(top_builddir)/src/utils/libutils.la				\
	$(top_builddir)/src/witness/libwitness.la			\
	$(top_builddir)/src/sat/minisat/libminisat.la			\
	$(top_builddir)/src/sat/libsat.la				\
	$(top_builddir)/src/dd/libcudd.la -lantlr3c			\
	$(BOOST_PROGRAM_OPTIONS_LIBS) -lboost_unit_test_framework

yasmv_LDFLAGS = $(BOOST_REGEX_LDFLAGS)
tests_LDFLAGS = $(BOOST_REGEX_LDFLAGS)

pkgconfdir = $(libdir)/pkgconfig
pkgconf_DATA = gnusmv.pc