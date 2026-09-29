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
EXTRA_DIST_CADICAL = tests/test_cadical_api.cc tests/test_cadical_runner.py tools/test-cadical-api.py docs/CADICAL_API_VALIDATION.md docs/CADICAL_OWNED_TYPES.md docs/CADICAL_BACKEND.md docs/CADICAL_MIGRATION_VALIDATION.md docs/SAT_SOLVER_PARAMETERS.md
EXTRA_DIST_CADICAL += cadical_integration.md docs/benchmarks/cadical-m1-minisat.md \
    docs/benchmarks/cadical-m1-minisat-reachable.json docs/benchmarks/cadical-m1-minisat-unreachable.json \
    docs/benchmarks/cadical-m6.md docs/benchmarks/cadical-m6-reachable.json docs/benchmarks/cadical-m6-unreachable.json
EXTRA_DIST_CADICAL += docs/benchmarks/cadical-release.md \
    docs/benchmarks/cadical-release-reachable.json docs/benchmarks/cadical-release-unreachable.json
EXTRA_DIST = tests/test_llvm2smv_stack.py tests/test_llvm2smv_memory.py tools/verify-c.py tools/llvm2smv_c.py tests/test_llvm2smv_c.py tools/llvm2smv_translate.py tests/test_llvm2smv_scalar.py tests/test_llvm2smv_model.py tools/llvm2smv_artifact.py tests/test_llvm2smv.py tests/llvm2smv docs/LLVM2SMV_IMPLEMENTATION_PLAN.md \
    tests/test_progress.py docs/PROGRESS_CHECKING.md docs/PROGRESS_CHECKING_PLAN.md docs/benchmarks/m6-progress.json \
    examples/progress/README.md examples/progress/complete.smv examples/progress/stalled.smv examples/progress/retry-forever.smv \
    docs/formats/progress-counterexample-v1.schema.json docs/formats/progress-proof-v1.schema.json \
    tools/test-support.sh tools/run-short-tests.sh tools/run-functional-tests.sh \
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
    tools/scenario/__init__.py tools/scenario/__main__.py tools/scenario/format.py tools/scenario/replay.py tools/workbench/sessions.py tests/test_analysis.py tests/test_sessions.py \
    docs/STRONGER_ANALYSIS.md docs/formats/analysis-v1.schema.json tools/benchmark-sessions.py \
    docs/benchmarks/m4-sessions.json src/workbench.hh tools/workbench/client.py tools/workbench/cli.py tools/workbench/launch.py tools/workbench/native.py tests/test_cli.py docs/CLI_WORKBENCH.md docs/formats/cli-v1.schema.json $(EXTRA_DIST_CADICAL)
EXTRA_DIST += README.md setup.sh tests/test_setup.py
EXTRA_DIST += tests/test_cadical_configure.py
EXTRA_DIST += docs/INTERPOLATION_PLAN.md docs/INTERPOLATION_PROOF_VALIDATION.md

AM_CPPFLAGS = -DYASMV_CLIENT_SOURCE=\"$(abs_top_srcdir)\" -DYASMV_CLIENT_DATA=\"$(pkgdatadir)\" \
-I$(top_srcdir)/src -I$(top_srcdir)/src/dd            \
-I$(top_srcdir)/src/enc -I$(top_srcdir)/src/expr                    \
-I$(top_srcdir)/src/type -I$(top_srcdir)/src/symb                   \
-I$(top_srcdir)/src/expr/walker -I$(top_srcdir)/src/expr/printer    \
-I$(top_srcdir)/src/model          \
-I$(top_srcdir)/src/cmd -I$(top_srcdir)/src/utils                   \
-I$(top_srcdir)/src/witness -I$(top_srcdir)/src/3rdparty/ezlogger   \
-I$(top_srcdir)/src/parser/grammars -I$(top_srcdir)/src/algorithms  \
-I$(top_srcdir)/src/3rdparty/ezlogger -I$(top_srcdir)/src/sat       \
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd                              \
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr                               \
-I$(top_srcdir)/src/dd/cudd-2.5.0/st                                \
-I$(top_srcdir)/src/dd/cudd-2.5.0/util                              \
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

bin_PROGRAMS = yasmv
EXTRA_PROGRAMS = yasmv_tests yasmv_reliability_tests yasmv_query_tests yasmv_interpolation_tests yasmv_interpolation_search_tests sat_literal_tests cadical_proof_tests

cadical_proof_tests_SOURCES = tests/test_cadical_proof.cc src/sat/proof.cc src/sat/proof.hh src/sat/proof_tracer.hh src/sat/circuit.cc src/sat/circuit.hh
cadical_proof_tests_CPPFLAGS = -I$(top_srcdir)/src $(CADICAL_CPPFLAGS)
cadical_proof_tests_LDADD = $(CADICAL_LIBS)

cadical-proof-test: cadical_proof_tests
	./cadical_proof_tests

.PHONY: cadical-proof-test

interpolation-test: yasmv_interpolation_tests yasmv_interpolation_search_tests
	YASMV_HOME="$(abs_top_srcdir)" ./yasmv_interpolation_tests --log_level=error
	YASMV_HOME="$(abs_top_srcdir)" ./yasmv_interpolation_search_tests --log_level=error

.PHONY: interpolation-test

sat_literal_tests_SOURCES = tests/test_sat_literals.cc
sat_literal_tests_CPPFLAGS = -I$(top_srcdir)/src

sat-types-test: sat_literal_tests
	./sat_literal_tests

.PHONY: sat-types-test
nobase_dist_pkgdata_DATA = docs/PROGRESS_CHECKING.md docs/PROGRESS_CHECKING_PLAN.md docs/benchmarks/m6-progress.json examples/progress/*.smv examples/progress/README.md microcode/* help/* tools/workbench/*.py tools/scenario/*.py \
    tools/workbench/static/* examples/retry-protocol/*.smv examples/retry-protocol/*.json \
    examples/retry-protocol/runner.py examples/retry-protocol/README.md docs/formats/*.json

# test target helper
short-test: yasmv
	@tools/run-short-tests.sh

unit-test: yasmv yasmv_tests
	@YASMV_HOME=`pwd` ./yasmv_tests --log_level=all

functional-test: yasmv yasmv_tests
	@tools/run-functional-tests.sh
if ENABLE_LLVM2SMV
llvm-test: yasmv
	@$(MAKE) -C llvm2smv test
else
llvm-test:
	@echo "LLVM tests disabled in this core-only build."
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

analysis-test: yasmv
	@YASMV_HOME=`pwd` python3 tests/test_analysis.py
	@YASMV_HOME=`pwd` python3 tests/test_interpolation_query.py
	@YASMV_HOME=`pwd` python3 tests/test_interpolation_benchmark.py
	@YASMV_HOME=`pwd` python3 tests/test_sessions.py

cli-test: yasmv
	@YASMV_HOME=`pwd` python3 tests/test_cli.py

progress-test: yasmv
	YASMV_HOME="$(abs_top_srcdir)" python3 $(srcdir)/tests/test_progress.py

test: llvm-test progress-test cli-test short-test unit-test functional-test reliability-test query-test workbench-test developer-workflow-test analysis-test cadical-runner-test cadical-proof-test interpolation-test sat-types-test setup-test cadical-configure-test
	@echo -e "\033[1;32m*** All tests passed Ok\033[0m"

.PHONY: llvm-test

setup-test:
	python3 $(srcdir)/tests/test_setup.py

.PHONY: setup-test

cadical-configure-test:
	python3 $(srcdir)/tests/test_cadical_configure.py

.PHONY: cadical-configure-test

# Opt-in raw API probe against an explicit upstream checkout. Never downloads code.
CADICAL_SOURCE ?=
cadical-runner-test:
	python3 $(srcdir)/tests/test_cadical_runner.py

cadical-api-test: cadical-runner-test
	@test -n "$(CADICAL_SOURCE)" || { echo 'Set CADICAL_SOURCE to the pinned CaDiCaL checkout.' >&2; exit 1; }
	python3 $(srcdir)/tools/test-cadical-api.py --source "$(CADICAL_SOURCE)" --suite all --cxx "$(CXX)" --cxxflags="$(CXXFLAGS)"

.PHONY: cadical-api-test cadical-runner-test

.PHONY: microcode
microcode:
	@tar cfj microcode.tar.bz2 microcode/

# tags target helper  (uses exuberant ctags)
tags:
	@find $(top_srcdir) -name "*.hh" -o -name "*.cc" | xargs etags

query_sources = src/workbench.cc src/query/runtime.cc src/query/source.cc src/query/query.cc src/query/trace.cc src/query/io.cc src/query/explain.cc src/query/property.cc src/query/interpolation.cc src/query/progress.cc src/query/session.cc
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
		$(top_builddir)/src/dd/libcudd.la $(CADICAL_LIBS)		\
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
		$(top_builddir)/src/dd/libcudd.la $(CADICAL_LIBS)		\
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

yasmv_interpolation_tests_SOURCES = $(query_sources) src/parse.cc src/test/main.cc src/test/test_interpolation.cc
yasmv_interpolation_tests_LDADD = $(yasmv_tests_LDADD)
yasmv_interpolation_tests_LDFLAGS = $(yasmv_tests_LDFLAGS)

EXTRA_DIST += tests/models/interpolation.smv

yasmv_interpolation_search_tests_SOURCES = $(query_sources) src/parse.cc src/test/main.cc src/test/test_interpolation_search.cc
yasmv_interpolation_search_tests_LDADD = $(yasmv_tests_LDADD)
yasmv_interpolation_search_tests_LDFLAGS = $(yasmv_tests_LDFLAGS)
EXTRA_DIST += tests/models/interpolation-search.smv

EXTRA_DIST += docs/formats/invariant-v1.schema.json

EXTRA_DIST += tests/test_interpolation_query.py
EXTRA_DIST += tools/benchmark-interpolation.py tests/test_interpolation_benchmark.py \
    tests/benchmarks/interpolation/cases.json tests/benchmarks/interpolation/*.smv \
    tests/benchmarks/interpolation/*.ll docs/INTERPOLATION_BENCHMARKS.md \
    docs/benchmarks/interpolation-m5.json
