AM_CPPFLAGS = @AM_CPPFLAGS@
AM_CFLAGS = @AM_CFLAGS@
AM_CXXFLAGS = -Wno-unused-variable -Wno-unused-function

INCLUDES = -I$(top_srcdir)/src/ -I$(top_srcdir)/src/dd		\
-I$(top_srcdir)/src/enc -I$(top_srcdir)/src/expr		\
-I$(top_srcdir)/src/model -I$(top_srcdir)/src/3rdparty/ezlogger	\
-I$(top_srcdir)/src/sat/core -I$(top_srcdir)/src/sat/mtl	\
-I$(top_srcdir)/src/sat/proof -I$(top_srcdir)/src/sat/utils	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/epd				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj


PKG_HH = satdefs.hh sat.hh proof/simple.hh proof/interpolator.hh	\
proof/proof.hh terms/terms.hh terms/ddterms.hh core/SolverTypes.hh	\
core/Solver.hh mtl/Alloc.hh mtl/Sort.hh mtl/Set.hh mtl/Heap.hh		\
mtl/Map.hh mtl/Alg.hh mtl/Vec.hh mtl/IntTypes.hh mtl/Queue.hh		\
mtl/XAlloc.hh utils/Options.hh utils/solverlogger.hh utils/System.hh	\
utils/ParseUtils.hh

PKG_CC = proof/proof.cc core/Solver.cc utils/Options.cc cnf.cc	\
logger.cc interpolator.cc solver.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libminisat.la
libminisat_la_SOURCES = $(PKG_SOURCES)
