AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = fsm reach sim

AM_CPPFLAGS=@AM_CPPFLAGS@ -I$(top_srcdir)/src	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CXXFLAGS=@AM_CXXFLAGS@

PKG_HH = base.hh exceptions.hh
PKG_CC = base.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libalgorithms.la
libalgorithms_la_SOURCES = $(PKG_HH) $(PKG_CC)
