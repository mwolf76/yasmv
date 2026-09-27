AUTOMAKE_OPTIONS = subdir-objects
AM_CPPFLAGS = -I$(top_srcdir)/llvm2smv/include $(LLVM_CPPFLAGS)
AM_CXXFLAGS = -std=c++20 -Wall
bin_PROGRAMS = llvm2smv

# The historical writer is quarantined: it is neither linked nor callable.
model_sources = src/transition_system.cc src/model_writer.cc
llvm2smv_SOURCES = src/main.cc src/module_analysis.cc src/scalar_lowering.cc src/memory_model.cc $(model_sources)
check_PROGRAMS = llvm2smv_model_tests
llvm2smv_model_tests_SOURCES = tests/model_tests.cc $(model_sources)
llvm2smv_model_tests_LDFLAGS = $(LLVM_LDFLAGS)
llvm2smv_model_tests_LDADD = $(LLVM_LIBS)
noinst_HEADERS = include/llvm2smv/module_analysis.hh include/llvm2smv/scalar_lowering.hh include/llvm2smv/memory_model.hh \
    include/llvm2smv/transition_system.hh include/llvm2smv/model_writer.hh
llvm2smv_LDFLAGS = $(LLVM_LDFLAGS)
llvm2smv_LDADD = $(LLVM_LIBS)

EXTRA_DIST = README.md DESIGN.md MODEL_FORMAT.md SCALAR_MODEL.md MEMORY_MODEL.md CALL_STACK.md C_WORKFLOW.md runtime/assert.h runtime/yasmv.h build.sh examples/simple/counter.c \
    examples/simple/conditional.c examples/simple/compile.sh \
    src/llvm2smv_pass.cc src/expr_translator.cc src/type_translator.cc src/smv_writer.cc \
    include/llvm2smv/llvm2smv_pass.hh include/llvm2smv/expr_translator.hh \
    include/llvm2smv/type_translator.hh include/llvm2smv/smv_writer.hh include/llvm2smv/concepts.hh

check-local: llvm2smv llvm2smv_model_tests
	LLVM2SMV="$(abs_builddir)/llvm2smv" CLANG="$(CLANG)" LLVM_OPT="$(LLVM_OPT)" \
	LLVM_LINK="$(LLVM_LINK)" python3 "$(top_srcdir)/tests/test_llvm2smv.py"

	./llvm2smv_model_tests
	LLVM2SMV_MODEL_TESTS="$(abs_builddir)/llvm2smv_model_tests" \
	YASMV="$${YASMV:-$(abs_top_builddir)/yasmv}" YASMV_HOME="$${YASMV_HOME:-$(abs_top_srcdir)}" \
	python3 "$(top_srcdir)/tests/test_llvm2smv_model.py"

	LLVM2SMV="$(abs_builddir)/llvm2smv" CLANG="$(CLANG)" \
	YASMV="$${YASMV:-$(abs_top_builddir)/yasmv}" YASMV_HOME="$${YASMV_HOME:-$(abs_top_srcdir)}" \
	python3 "$(top_srcdir)/tests/test_llvm2smv_scalar.py"

	LLVM2SMV="$(abs_builddir)/llvm2smv" CLANG="$(CLANG)" LLVM_LINK="$(LLVM_LINK)" \
	YASMV="$${YASMV:-$(abs_top_builddir)/yasmv}" YASMV_HOME="$${YASMV_HOME:-$(abs_top_srcdir)}" \
	python3 "$(top_srcdir)/tests/test_llvm2smv_c.py"

	LLVM2SMV="$(abs_builddir)/llvm2smv" CLANG="$(CLANG)" LLVM_LINK="$(LLVM_LINK)" \
	YASMV="$${YASMV:-$(abs_top_builddir)/yasmv}" YASMV_HOME="$${YASMV_HOME:-$(abs_top_srcdir)}" \
	python3 "$(top_srcdir)/tests/test_llvm2smv_memory.py"

	LLVM2SMV="$(abs_builddir)/llvm2smv" CLANG="$(CLANG)" LLVM_LINK="$(LLVM_LINK)" \
	YASMV="$${YASMV:-$(abs_top_builddir)/yasmv}" YASMV_HOME="$${YASMV_HOME:-$(abs_top_srcdir)}" \
	python3 "$(top_srcdir)/tests/test_llvm2smv_stack.py"

test: check-local

.PHONY: test check-local
