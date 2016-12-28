AUTOMAKE_OPTIONS = subdir-objects

AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = enc.hh enc_mgr.hh tcbi.hh ucbi.hh

PKG_CC = enc.cc enc_mgr.cc monolithic.cc algebraic.cc array.cc	\
ucbi.cc tcbi.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libenc.la
libenc_la_SOURCES = $(PKG_HH) $(PKG_CC)
