AUTOMAKE_OPTIONS = subdir-objects
AM_CPPFLAGS = -I$(top_srcdir)/llvm2smv/include $(LLVM_CPPFLAGS)
AM_CXXFLAGS = -std=c++20 -Wall
bin_PROGRAMS = llvm2smv

# The historical writer is quarantined: it is neither linked nor callable.
llvm2smv_SOURCES = src/main.cc src/module_analysis.cc
noinst_HEADERS = include/llvm2smv/module_analysis.hh
llvm2smv_LDFLAGS = $(LLVM_LDFLAGS)
llvm2smv_LDADD = $(LLVM_LIBS)

EXTRA_DIST = README.md DESIGN.md build.sh examples/simple/counter.c \
    examples/simple/conditional.c examples/simple/compile.sh \
    src/llvm2smv_pass.cc src/expr_translator.cc src/type_translator.cc src/smv_writer.cc \
    include/llvm2smv/llvm2smv_pass.hh include/llvm2smv/expr_translator.hh \
    include/llvm2smv/type_translator.hh include/llvm2smv/smv_writer.hh include/llvm2smv/concepts.hh

check-local: llvm2smv
	LLVM2SMV="$(abs_builddir)/llvm2smv" CLANG="$(CLANG)" LLVM_OPT="$(LLVM_OPT)" \
	LLVM_LINK="$(LLVM_LINK)" python3 "$(top_srcdir)/tests/test_llvm2smv.py"

test: check-local

.PHONY: test check-local
