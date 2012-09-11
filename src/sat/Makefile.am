AM_CPPFLAGS = @AM_CPPFLAGS@
AM_CFLAGS = @AM_CFLAGS@
AM_CXXFLAGS = -Wno-unused-variable -Wno-unused-function -DINT32_MIN=-1	\
-DINT32_MAX=200 -DINT64_MIN=-1 -DINT64_MAX=200

INCLUDES = -I$(top_srcdir)/src/ -I$(top_srcdir)/src/expr	\
-I$(top_srcdir)/src/model -I$(top_srcdir)/src/3rdparty/ezlogger	\
-I$(top_srcdir)/src/sat/core -I$(top_srcdir)/src/sat/mtl	\
-I$(top_srcdir)/src/sat/proof -I$(top_srcdir)/src/sat/utils	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/epd				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj


PKG_HH = sat.hh bdd_sat.hh cnf/cnf.hh cnf/bdd_cnf.hh model/model.hh	\
proof/simple.hh proof/interpolator.hh proof/proof.hh proof/terms.hh	\
core/SolverTypes.hh core/Solver.hh mtl/Alloc.hh mtl/Sort.hh mtl/Set.hh	\
mtl/Heap.hh mtl/Map.hh mtl/Alg.hh mtl/Vec.hh mtl/IntTypes.hh		\
mtl/Queue.hh mtl/XAlloc.hh utils/Options.hh utils/solverlogger.hh	\
utils/System.hh utils/ParseUtils.hh

PKG_CC = bdd_sat.cc cnf/bdd_cnf.cc model/bdd_model.cc		\
proof/interpolator.cc proof/bdd_interpolator.cc proof/proof.cc	\
core/Solver.cc utils/solverlogger.cc utils/Options.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libminisat.la
libminisat_la_SOURCES = $(PKG_SOURCES)
