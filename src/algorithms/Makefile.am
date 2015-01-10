AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = bmc sim

AM_CPPFLAGS=@AM_CPPFLAGS@ -I$(top_srcdir)/src	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CXXFLAGS=@AM_CXXFLAGS@

PKG_HH = base.hh init.hh
PKG_CC = base.cc init.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libalgorithms.la
libalgorithms_la_SOURCES = $(PKG_SOURCES)
