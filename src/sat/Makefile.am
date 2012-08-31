AM_CPPFLAGS = @AM_CPPFLAGS@
AM_CFLAGS = @AM_CFLAGS@
AM_CXXFLAGS = -Wno-unused-variable -Wno-unused-function -DINT32_MIN=-1 -DINT32_MAX=200 -DINT64_MIN=-1 -DINT64_MAX=200

INCLUDES = \
	-I$(top_srcdir)/src/sat/core 				\
	-I$(top_srcdir)/src/sat/mtl		 	      	\
	-I$(top_srcdir)/src/sat/proof				\
	-I$(top_srcdir)/src/sat/utils

PKG_HH = proof/simple.hh proof/interpolator.hh proof/proof.hh		\
proof/terms.hh core/SolverTypes.hh core/Solver.hh mtl/Alloc.hh		\
mtl/Sort.hh mtl/Set.hh mtl/Heap.hh mtl/Map.hh mtl/Alg.hh mtl/Vec.hh	\
mtl/IntTypes.hh mtl/Queue.hh mtl/XAlloc.hh utils/Options.hh		\
utils/solverlogger.hh utils/System.hh utils/ParseUtils.hh		\
utils/singleton.hh utils/logger.hh

PKG_CC = proof/interpolator.cc proof/proof.cc core/Solver.cc	\
utils/logger.cc utils/System.cc utils/solverlogger.cc		\
utils/Options.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libminisat.la
libminisat_la_SOURCES = $(PKG_SOURCES)
