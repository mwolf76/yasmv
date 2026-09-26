if ENABLE_LLVM2SMV
SUBDIRS = src doc man llvm2smv
else
SUBDIRS = src doc man
endif
AUTOMAKE_OPTIONS = subdir-objects

ACLOCAL_AMFLAGS = -I m4

PACKAGE = $(PACKAGE_NAME)
VERSION = $(PACKAGE_VERSION)

READMES = LGPL-2.1 NEWS README
EXTRA_DIST = tools/test-support.sh tools/run-short-tests.sh tools/run-functional-tests.sh \
    tools/build-provenance.py tests/test_regressions.py docs/CORRECTNESS_BASELINE.md \
    src/query/query.hh src/query/runtime.hh src/query/source.hh src/query/trace.hh src/query/expressions.hh \
    tools/run-query.py tests/test_query.py tests/models/query.smv \
    docs/QUERY_AND_TRACE_CONTRACTS.md \
    docs/formats/query-v1.schema.json docs/formats/trace-v1.schema.json \
    docs/WORKBENCH.md docs/formats/workbench-v1.schema.json docs/formats/scenario-v1.schema.json \
    tools/workbench/__init__.py tools/workbench/__main__.py tools/workbench/protocol.py \
    tools/workbench/engine.py tools/workbench/server.py tools/workbench/static/index.html \
    tools/workbench/static/style.css tools/workbench/static/app.js \
    examples/retry-protocol/README.md examples/retry-protocol/faulty.smv \
    examples/retry-protocol/deduplicating.smv examples/retry-protocol/scenario.json \
    examples/retry-protocol/runner.py tests/test_workbench.py tests/workbench-browser.cjs \
    tests/test_explanations.py tests/test_scenarios.py docs/EXPLANATIONS_AND_SCENARIOS.md \
    docs/formats/explanation-v1.schema.json docs/formats/executable-scenario-v1.schema.json \
    tools/scenario/__init__.py tools/scenario/__main__.py tools/scenario/format.py tools/scenario/replay.py

AM_CPPFLAGS = -I$(top_srcdir)/src -I$(top_srcdir)/src/dd            \
-I$(top_srcdir)/src/enc -I$(top_srcdir)/src/expr                    \
-I$(top_srcdir)/src/type -I$(top_srcdir)/src/symb                   \
-I$(top_srcdir)/src/expr/walker -I$(top_srcdir)/src/expr/printer    \
-I$(top_srcdir)/src/model          \
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
EXTRA_PROGRAMS = yasmv_tests yasmv_reliability_tests yasmv_query_tests
nobase_dist_pkgdata_DATA = microcode/* help/*

# test target helper
short-test: yasmv
	@tools/run-short-tests.sh

unit-test: yasmv yasmv_tests
	@YASMV_HOME=`pwd` ./yasmv_tests --log_level=all

functional-test: yasmv yasmv_tests
	@tools/run-functional-tests.sh
if ENABLE_LLVM2SMV
	@echo "Running llvm2smv tests..."
	@$(MAKE) -C llvm2smv test
endif

reliability-test: yasmv yasmv_reliability_tests
	@YASMV_HOME=`pwd` python3 tests/test_regressions.py
	@for settings in 000 001 010 011 100 101 110 111; do \
	    YASMV_HOME=`pwd` YASMV_TEST_CNF=$$settings ./yasmv_reliability_tests --log_level=error || exit 1; \
	done

query-test: yasmv yasmv_query_tests
	@YASMV_HOME=`pwd` ./yasmv_query_tests --log_level=error
	@YASMV_HOME=`pwd` python3 tests/test_query.py

workbench-test: yasmv
	@YASMV_HOME=`pwd` python3 tests/test_workbench.py

developer-workflow-test: yasmv
	@YASMV_HOME=`pwd` python3 tests/test_explanations.py
	@YASMV_HOME=`pwd` python3 tests/test_scenarios.py

test: short-test unit-test functional-test reliability-test query-test workbench-test developer-workflow-test
	@echo -e "\033[1;32m*** All tests passed Ok\033[0m"

.PHONY: microcode
microcode:
	@tar cfj microcode.tar.bz2 microcode/

# tags target helper  (uses exuberant ctags)
tags:
	@find $(top_srcdir) -name "*.hh" -o -name "*.cc" | xargs etags

query_sources = src/query/runtime.cc src/query/source.cc src/query/query.cc src/query/trace.cc src/query/io.cc src/query/explain.cc
yasmv_SOURCES = src/main.cc src/debug.cc src/parse.cc $(query_sources)

yasmv_LDADD = $(top_builddir)/src/parser/libparser.la				\
		$(top_builddir)/src/cmd/commands/libcommands.la			\
		$(top_builddir)/src/cmd/libcmd.la				\
		$(top_builddir)/src/algorithms/fsm/libfsm.la			\
		$(top_builddir)/src/algorithms/reach/libreach.la		\
		$(top_builddir)/src/algorithms/sim/libsim.la			\
		$(top_builddir)/src/algorithms/libalgorithms.la			\
		$(top_builddir)/src/model/libmodel.la				\
		$(top_builddir)/src/enc/libenc.la				\
		$(top_builddir)/src/env/libenv.la				\
		$(top_builddir)/src/model/analyzer/libanalyzer.la		\
		$(top_builddir)/src/model/type_checker/libtype_checker.la	\
		$(top_builddir)/src/expr/libexpr.la				\
		$(top_builddir)/src/expr/preprocessor/libpreprocessor.la	\
		$(top_builddir)/src/expr/walker/libexpr_walker.la		\
		$(top_builddir)/src/expr/printer/libprinter.la			\
		$(top_builddir)/src/expr/time/libexpr_time.la			\
		$(top_builddir)/src/expr/time/analyzer/libanalyzer.la			\
		$(top_builddir)/src/expr/time/expander/libexpander.la			\
		$(top_builddir)/src/type/libtype.la				\
		$(top_builddir)/src/symb/libsymb.la				\
		$(top_builddir)/src/utils/libutils.la				\
		$(top_builddir)/src/witness/libwitness.la			\
		$(top_builddir)/src/sat/libsat.la				\
		$(top_builddir)/src/compiler/libcompiler.la		\
		$(top_builddir)/src/common/libcommon.la				\
		$(top_builddir)/src/opts/libopts.la				\
										\
		$(top_builddir)/src/dd/libcudd.la $(MINISAT_LIBS)		\
		$(ANTLR_LIBS) $(LIBJSONCPP_LIBS) $(LIBYAMLCPP_LIBS)		\
		$(BOOST_PROGRAM_OPTIONS_LIBS)					\
		$(BOOST_FILESYSTEM_LIBS) $(BOOST_THREAD_LIBS)			\
		$(BOOST_CHRONO_LIBS) $(PTHREAD_LIBS)

yasmv_LDFLAGS = $(BOOST_REGEX_LDFLAGS) -L/usr/local/lib

yasmv_tests_SOURCES = $(query_sources) src/parse.cc src/test/main.cc		\
		src/test/test_expr.cc src/test/test_parser.cc	\
		src/test/test_type.cc src/test/test_dd.cc		\
		src/test/test_enc.cc src/test/test_compiler.cc

yasmv_tests_LDADD = $(top_builddir)/src/parser/libparser.la			\
		$(top_builddir)/src/cmd/commands/libcommands.la			\
		$(top_builddir)/src/cmd/libcmd.la				\
		$(top_builddir)/src/algorithms/fsm/libfsm.la			\
		$(top_builddir)/src/algorithms/reach/libreach.la		\
		$(top_builddir)/src/algorithms/sim/libsim.la			\
		$(top_builddir)/src/algorithms/libalgorithms.la			\
		$(top_builddir)/src/model/libmodel.la				\
		$(top_builddir)/src/enc/libenc.la				\
		$(top_builddir)/src/env/libenv.la				\
		$(top_builddir)/src/model/analyzer/libanalyzer.la		\
		$(top_builddir)/src/model/type_checker/libtype_checker.la	\
		$(top_builddir)/src/expr/libexpr.la				\
		$(top_builddir)/src/expr/preprocessor/libpreprocessor.la	\
		$(top_builddir)/src/expr/walker/libexpr_walker.la		\
		$(top_builddir)/src/expr/printer/libprinter.la			\
		$(top_builddir)/src/expr/time/libexpr_time.la			\
		$(top_builddir)/src/expr/time/analyzer/libanalyzer.la			\
		$(top_builddir)/src/expr/time/expander/libexpander.la			\
		$(top_builddir)/src/type/libtype.la				\
		$(top_builddir)/src/symb/libsymb.la				\
		$(top_builddir)/src/utils/libutils.la				\
		$(top_builddir)/src/witness/libwitness.la			\
		$(top_builddir)/src/sat/libsat.la				\
		$(top_builddir)/src/compiler/libcompiler.la		\
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

yasmv_reliability_tests_SOURCES = $(query_sources) src/parse.cc src/test/main.cc src/test/test_reliability.cc
yasmv_reliability_tests_LDADD = $(yasmv_tests_LDADD)
yasmv_reliability_tests_LDFLAGS = $(yasmv_tests_LDFLAGS)

pkgconfdir = $(libdir)/pkgconfig
pkgconf_DATA = yasmv.pc

yasmv_query_tests_SOURCES = $(query_sources) src/parse.cc src/test/main.cc src/test/test_query.cc
yasmv_query_tests_LDADD = $(yasmv_tests_LDADD)
yasmv_query_tests_LDFLAGS = $(yasmv_tests_LDFLAGS)
