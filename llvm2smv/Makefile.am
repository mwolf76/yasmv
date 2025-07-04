# llvm2smv Makefile.am

AUTOMAKE_OPTIONS = subdir-objects

# Include directories
AM_CPPFLAGS = -I$(top_srcdir)/llvm2smv/include $(LLVM_CPPFLAGS)

# C++20 standard requirement
AM_CXXFLAGS = -std=c++20 -Wall

# Binary target
bin_PROGRAMS = llvm2smv

# Sources
llvm2smv_SOURCES = \
	src/main.cc \
	src/llvm2smv_pass.cc \
	src/expr_translator.cc \
	src/type_translator.cc \
	src/smv_writer.cc

# Headers (for distribution)
noinst_HEADERS = \
	include/llvm2smv/llvm2smv_pass.hh \
	include/llvm2smv/expr_translator.hh \
	include/llvm2smv/type_translator.hh \
	include/llvm2smv/smv_writer.hh \
	include/llvm2smv/concepts.hh

# Linking
llvm2smv_LDFLAGS = $(LLVM_LDFLAGS)
llvm2smv_LDADD = $(LLVM_LIBS)

# Examples and documentation
EXTRA_DIST = \
	examples/simple/counter.c \
	examples/simple/counter.ll \
	examples/simple/compile.sh \
	design.md

# Test target
test-local:
	@echo "Testing llvm2smv..."
	@if test "x$(CLANG)" != "xno"; then \
		cd $(srcdir)/examples/simple && ./compile.sh counter.c && \
		$(abs_builddir)/llvm2smv counter.ll -o counter.smv && \
		echo "Generated counter.smv successfully!"; \
	else \
		echo "Skipping test - clang not available"; \
	fi

clean-local:
	-rm -f examples/simple/*.ll examples/simple/*.smv

# Make test target available
test: test-local

.PHONY: test test-local clean-local
