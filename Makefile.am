SUBDIRS = src doc
AUTOMAKE_OPTIONS = subdir-objects

ACLOCAL_AMFLAGS = -I m4

PACKAGE = $(PACKAGE_NAME)
VERSION = $(PACKAGE_VERSION)

READMES = LGPL-2.1 NEWS README

AM_CPPFLAGS = -I$(top_srcdir)/src -I$(top_srcdir)/src/dd            \
-I$(top_srcdir)/src/enc -I$(top_srcdir)/src/expr                    \
-I$(top_srcdir)/src/type -I$(top_srcdir)/src/symb                   \
-I$(top_srcdir)/src/expr/walker -I$(top_srcdir)/src/expr/printer    \
-I$(top_srcdir)/src/expr/nnfizer -I$(top_srcdir)/src/model          \
-I$(top_srcdir)/src/cmd -I$(top_srcdir)/src/utils                   \
-I$(top_srcdir)/src/witness -I$(top_srcdir)/src/3rdparty/ezlogger   \
-I$(top_srcdir)/src/parser/grammars -I$(top_srcdir)/src/algorithms  \
-I$(top_srcdir)/src/3rdparty/ezlogger -I$(top_srcdir)/src/sat/core  \
-I$(top_srcdir)/src/sat -I$(top_srcdir)/src/sat/mtl                 \
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd                              \
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr                               \
-I$(top_srcdir)/src/dd/cudd-2.5.0/st                                \
-I$(top_srcdir)/src/dd/cudd-2.5.0/util                              \
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

bin_PROGRAMS = yasmv
EXTRA_PROGRAMS = yasmv_tests
nobase_dist_pkgdata_DATA = microcode/* help/*

# test target helper
unittest: yasmv_tests
	YASMV_HOME=`pwd` ./yasmv_tests --log_level=all

functionaltest: yasmv_tests
	@tools/run-functional-tests.sh

test: unittest functionaltest
	@echo "*** All tests passed Ok"

.PHONY: microcode
microcode:
	@tar cfj microcode.tar.bz2 microcode/

# tags target helper  (uses exuberant ctags)
tags:
	@find $(top_srcdir) -name "*.hh" -o -name "*.cc" | xargs etags

yasmv_SOURCES = src/main.cc src/parse.cc

yasmv_LDADD = $(top_builddir)/src/parser/libparser.la				\
		$(top_builddir)/src/cmd/commands/libcommands.la			\
		$(top_builddir)/src/cmd/libcmd.la				\
		$(top_builddir)/src/algorithms/check/libcheck.la		\
		$(top_builddir)/src/algorithms/fsm/libfsm.la			\
		$(top_builddir)/src/algorithms/reach/libreach.la		\
		$(top_builddir)/src/algorithms/sim/libsim.la			\
		$(top_builddir)/src/algorithms/libalgorithms.la			\
		$(top_builddir)/src/model/libmodel.la				\
		$(top_builddir)/src/model/compiler/libcompiler.la		\
		$(top_builddir)/src/enc/libenc.la				\
		$(top_builddir)/src/env/libenv.la				\
		$(top_builddir)/src/model/analyzer/libanalyzer.la		\
		$(top_builddir)/src/model/type_checker/libtype_checker.la	\
		$(top_builddir)/src/model/preprocessor/libpreprocessor.la	\
		$(top_builddir)/src/expr/libexpr.la				\
		$(top_builddir)/src/expr/walker/libexpr_walker.la		\
		$(top_builddir)/src/expr/printer/libprinter.la			\
		$(top_builddir)/src/expr/nnfizer/libnnfizer.la			\
		$(top_builddir)/src/type/libtype.la				\
		$(top_builddir)/src/symb/libsymb.la				\
		$(top_builddir)/src/utils/libutils.la				\
		$(top_builddir)/src/witness/libwitness.la			\
		$(top_builddir)/src/sat/libsat.la				\
		$(top_builddir)/src/common/libcommon.la				\
		$(top_builddir)/src/opts/libopts.la				\
										\
		$(top_builddir)/src/dd/libcudd.la $(MINISAT_LIBS)		\
		$(ANTLR_LIBS) $(LIBJSONCPP_LIBS) $(LIBYAMLCPP_LIBS)		\
		$(BOOST_PROGRAM_OPTIONS_LIBS)					\
		$(BOOST_FILESYSTEM_LIBS) $(BOOST_THREAD_LIBS)			\
		$(BOOST_CHRONO_LIBS) $(PTHREAD_LIBS)

yasmv_LDFLAGS = $(BOOST_REGEX_LDFLAGS) -L/usr/local/lib

yasmv_tests_SOURCES = src/parse.cc testing/tests.cc		\
		testing/test_expr.cc testing/test_parser.cc	\
		testing/test_type.cc testing/test_dd.cc		\
		testing/test_enc.cc testing/test_compiler.cc

yasmv_tests_LDADD = $(top_builddir)/src/parser/libparser.la			\
		$(top_builddir)/src/cmd/commands/libcommands.la			\
		$(top_builddir)/src/cmd/libcmd.la				\
		$(top_builddir)/src/algorithms/check/libcheck.la		\
		$(top_builddir)/src/algorithms/fsm/libfsm.la			\
		$(top_builddir)/src/algorithms/reach/libreach.la		\
		$(top_builddir)/src/algorithms/sim/libsim.la			\
		$(top_builddir)/src/algorithms/libalgorithms.la			\
		$(top_builddir)/src/model/libmodel.la				\
		$(top_builddir)/src/model/compiler/libcompiler.la		\
		$(top_builddir)/src/enc/libenc.la				\
		$(top_builddir)/src/env/libenv.la				\
		$(top_builddir)/src/model/analyzer/libanalyzer.la		\
		$(top_builddir)/src/model/type_checker/libtype_checker.la	\
		$(top_builddir)/src/model/preprocessor/libpreprocessor.la	\
		$(top_builddir)/src/expr/libexpr.la				\
		$(top_builddir)/src/expr/walker/libexpr_walker.la		\
		$(top_builddir)/src/expr/printer/libprinter.la			\
		$(top_builddir)/src/expr/nnfizer/libnnfizer.la			\
		$(top_builddir)/src/type/libtype.la				\
		$(top_builddir)/src/symb/libsymb.la				\
		$(top_builddir)/src/utils/libutils.la				\
		$(top_builddir)/src/witness/libwitness.la			\
		$(top_builddir)/src/sat/libsat.la				\
		$(top_builddir)/src/common/libcommon.la				\
		$(top_builddir)/src/opts/libopts.la				\
										\
		$(top_builddir)/src/dd/libcudd.la $(MINISAT_LIBS)		\
		$(ANTLR_LIBS) $(LIBJSONCPP_LIBS) $(LIBYAMLCPP_LIBS)		\
		$(BOOST_PROGRAM_OPTIONS_LIBS)					\
		$(BOOST_FILESYSTEM_LIBS) $(BOOST_THREAD_LIBS)			\
		$(BOOST_CHRONO_LIBS) $(PTHREAD_LIBS)				\
		-lboost_unit_test_framework

yasmv_tests_LDFLAGS = $(BOOST_REGEX_LDFLAGS) -L/usr/local/lib

pkgconfdir = $(libdir)/pkgconfig
pkgconf_DATA = yasmv.pc

