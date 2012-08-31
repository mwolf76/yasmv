AM_CPPFLAGS = @AM_CPPFLAGS@ -DSIZEOF_VOID_P@SIZEOF_VOID_P@ -DSIZEOF_INT@SIZEOF_INT@ -DSIZEOF_LONG@SIZEOF_LONG@
AM_CFLAGS = @AM_CFLAGS@
AM_CXXFLAGS = -Wno-unused-variable -Wno-unused-function

INCLUDES = \
	-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd          \
	-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr 	 	\
	-I$(top_srcdir)/src/dd/cudd-2.5.0/epd		\
	-I$(top_srcdir)/src/dd/cudd-2.5.0/st		\
	-I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
	-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

PKG_HH = cudd-2.5.0/cudd/cudd.hc cudd-2.5.0/cudd/cuddInt.h
PKG_CC = cuddDownloaded.cc 					\
cudd-2.5.0/cudd/cuddAPI.c cudd-2.5.0/cudd/cuddAddAbs.c		\
cudd-2.5.0/cudd/cuddAddApply.c cudd-2.5.0/cudd/cuddAddFind.c	\
cudd-2.5.0/cudd/cuddAddIte.c cudd-2.5.0/cudd/cuddAddInv.c	\
cudd-2.5.0/cudd/cuddAddNeg.c cudd-2.5.0/cudd/cuddAddWalsh.c	\
cudd-2.5.0/cudd/cuddAndAbs.c cudd-2.5.0/cudd/cuddAnneal.c	\
cudd-2.5.0/cudd/cuddApa.c cudd-2.5.0/cudd/cuddApprox.c		\
cudd-2.5.0/cudd/cuddBddAbs.c cudd-2.5.0/cudd/cuddBddCorr.c	\
cudd-2.5.0/cudd/cuddBddIte.c cudd-2.5.0/cudd/cuddBridge.c	\
cudd-2.5.0/cudd/cuddCache.c cudd-2.5.0/cudd/cuddCheck.c		\
cudd-2.5.0/cudd/cuddClip.c cudd-2.5.0/cudd/cuddCof.c		\
cudd-2.5.0/cudd/cuddCompose.c cudd-2.5.0/cudd/cuddDecomp.c	\
cudd-2.5.0/cudd/cuddEssent.c cudd-2.5.0/cudd/cuddExact.c	\
cudd-2.5.0/cudd/cuddExport.c cudd-2.5.0/cudd/cuddGenCof.c	\
cudd-2.5.0/cudd/cuddGenetic.c cudd-2.5.0/cudd/cuddGroup.c	\
cudd-2.5.0/cudd/cuddHarwell.c cudd-2.5.0/cudd/cuddInit.c	\
cudd-2.5.0/cudd/cuddInteract.c cudd-2.5.0/cudd/cuddLCache.c	\
cudd-2.5.0/cudd/cuddLevelQ.c cudd-2.5.0/cudd/cuddLinear.c	\
cudd-2.5.0/cudd/cuddLiteral.c cudd-2.5.0/cudd/cuddMatMult.c	\
cudd-2.5.0/cudd/cuddPriority.c cudd-2.5.0/cudd/cuddRead.c	\
cudd-2.5.0/cudd/cuddRef.c cudd-2.5.0/cudd/cuddReorder.c		\
cudd-2.5.0/cudd/cuddSat.c cudd-2.5.0/cudd/cuddSign.c		\
cudd-2.5.0/cudd/cuddSolve.c cudd-2.5.0/cudd/cuddSplit.c		\
cudd-2.5.0/cudd/cuddSubsetHB.c cudd-2.5.0/cudd/cuddSubsetSP.c	\
cudd-2.5.0/cudd/cuddSymmetry.c cudd-2.5.0/cudd/cuddTable.c	\
cudd-2.5.0/cudd/cuddUtil.c cudd-2.5.0/cudd/cuddWindow.c		\
cudd-2.5.0/cudd/cuddZddCount.c cudd-2.5.0/cudd/cuddZddFuncs.c	\
cudd-2.5.0/cudd/cuddZddGroup.c cudd-2.5.0/cudd/cuddZddIsop.c	\
cudd-2.5.0/cudd/cuddZddLin.c cudd-2.5.0/cudd/cuddZddMisc.c	\
cudd-2.5.0/cudd/cuddZddPort.c cudd-2.5.0/cudd/cuddZddReord.c	\
cudd-2.5.0/cudd/cuddZddSetop.c cudd-2.5.0/cudd/cuddZddSymm.c	\
cudd-2.5.0/cudd/cuddZddUtil.c cudd-2.5.0/epd/epd.c		\
cudd-2.5.0/mtr/mtrGroup.c \ cudd-2.5.0/mtr/mtrBasic.c		\
cudd-2.5.0/obj/cuddObj.cc

cuddDownloaded.cc:
	@echo "downloading cudd-2.5.0 ... (this may take a while)"
	@wget ftp://vlsi.colorado.edu/pub/cudd-2.5.0.tar.gz
	@echo "unpacking cudd-2.5.0 ... (this may take a while)"
	@tar xfz cudd-2.5.0.tar.gz
	@touch cuddDownloaded.cc

distclean-local:
	@rm -rf cudd-2.5.0
	@rm -f cudd-2.5.0.tar.gz
	@rm -f cuddDownloaded.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libcudd.la
libcudd_la_SOURCES = $(PKG_SOURCES)
