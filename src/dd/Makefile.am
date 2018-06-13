AUTOMAKE_OPTIONS = subdir-objects

AM_CPPFLAGS = @AM_CPPFLAGS@ -DSIZEOF_VOID_P=@SIZEOF_VOID_P@	\
-DSIZEOF_INT=@SIZEOF_INT@ -DSIZEOF_LONG=@SIZEOF_LONG@		\
-I$(top_srcdir)/src/ -I$(top_srcdir)/src/expr			\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util				\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CFLAGS = @AM_CFLAGS@
AM_CXXFLAGS = -Wno-unused-variable -Wno-unused-function

CUDD_HH = cudd-2.5.0/mtr/mtr.h cudd-2.5.0/mtr/mtrInt.h			\
cudd-2.5.0/cudd/cuddInt.h cudd-2.5.0/cudd/cudd.h			\
cudd-2.5.0/obj/cuddObj.hh cudd-2.5.0/st/st.h cudd-2.5.0/util/util.h

PKG_HH = $(CUDD_HH) cudd_mgr.hh dd.hh dd_walker.hh

CUDD_CC = cudd-2.5.0/cudd/cuddAPI.c cudd-2.5.0/cudd/cuddAddAbs.c	\
cudd-2.5.0/cudd/cuddAddApply.c cudd-2.5.0/cudd/cuddAddFind.c		\
cudd-2.5.0/cudd/cuddAddIte.c cudd-2.5.0/cudd/cuddAddInv.c		\
cudd-2.5.0/cudd/cuddAddNeg.c cudd-2.5.0/cudd/cuddAddWalsh.c		\
cudd-2.5.0/cudd/cuddAndAbs.c cudd-2.5.0/cudd/cuddAnneal.c		\
cudd-2.5.0/cudd/cuddApprox.c cudd-2.5.0/cudd/cuddBddAbs.c		\
cudd-2.5.0/cudd/cuddBddCorr.c cudd-2.5.0/cudd/cuddBddIte.c		\
cudd-2.5.0/cudd/cuddBridge.c cudd-2.5.0/cudd/cuddCache.c		\
cudd-2.5.0/cudd/cuddCheck.c cudd-2.5.0/cudd/cuddClip.c			\
cudd-2.5.0/cudd/cuddCof.c cudd-2.5.0/cudd/cuddCompose.c			\
cudd-2.5.0/cudd/cuddDecomp.c cudd-2.5.0/cudd/cuddEssent.c		\
cudd-2.5.0/cudd/cuddExact.c cudd-2.5.0/cudd/cuddExport.c		\
cudd-2.5.0/cudd/cuddGenCof.c cudd-2.5.0/cudd/cuddGenetic.c		\
cudd-2.5.0/cudd/cuddGroup.c cudd-2.5.0/cudd/cuddHarwell.c		\
cudd-2.5.0/cudd/cuddInit.c cudd-2.5.0/cudd/cuddInteract.c		\
cudd-2.5.0/cudd/cuddLCache.c cudd-2.5.0/cudd/cuddLevelQ.c		\
cudd-2.5.0/cudd/cuddLinear.c cudd-2.5.0/cudd/cuddLiteral.c		\
cudd-2.5.0/cudd/cuddPriority.c cudd-2.5.0/cudd/cuddRef.c		\
cudd-2.5.0/cudd/cuddReorder.c cudd-2.5.0/cudd/cuddSat.c			\
cudd-2.5.0/cudd/cuddSign.c cudd-2.5.0/cudd/cuddSolve.c			\
cudd-2.5.0/cudd/cuddSplit.c cudd-2.5.0/cudd/cuddSubsetHB.c		\
cudd-2.5.0/cudd/cuddSubsetSP.c cudd-2.5.0/cudd/cuddSymmetry.c		\
cudd-2.5.0/cudd/cuddTable.c cudd-2.5.0/cudd/cuddUtil.c			\
cudd-2.5.0/cudd/cuddWindow.c cudd-2.5.0/cudd/cuddZddCount.c		\
cudd-2.5.0/cudd/cuddZddFuncs.c cudd-2.5.0/cudd/cuddZddGroup.c		\
cudd-2.5.0/cudd/cuddZddIsop.c cudd-2.5.0/cudd/cuddZddLin.c		\
cudd-2.5.0/cudd/cuddZddMisc.c cudd-2.5.0/cudd/cuddZddPort.c		\
cudd-2.5.0/cudd/cuddZddReord.c cudd-2.5.0/cudd/cuddZddSetop.c		\
cudd-2.5.0/cudd/cuddZddSymm.c cudd-2.5.0/cudd/cuddZddUtil.c		\
cudd-2.5.0/mtr/mtrGroup.c cudd-2.5.0/mtr/mtrBasic.c			\
cudd-2.5.0/util/cpu_stats.c cudd-2.5.0/util/datalimit.c			\
cudd-2.5.0/util/pathsearch.c cudd-2.5.0/util/prtime.c			\
cudd-2.5.0/util/restart.c cudd-2.5.0/util/saveimage.c			\
cudd-2.5.0/util/strsav.c cudd-2.5.0/util/texpand.c			\
cudd-2.5.0/util/cpu_time.c cudd-2.5.0/util/pipefork.c			\
cudd-2.5.0/util/safe_mem.c cudd-2.5.0/util/state.c			\
cudd-2.5.0/util/stub.c cudd-2.5.0/st/st.c cudd-2.5.0/obj/cuddObj.cc

PKG_CC = $(CUDD_CC) cudd_mgr.cc dd_walker.cc dd_leaf_walker.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libcudd.la
libcudd_la_SOURCES = $(PKG_HH) $(PKG_CC)
