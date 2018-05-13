AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = commands

AM_CPPFLAGS=@AM_CPPFLAGS@ -I$(top_srcdir)/src																	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd -I$(top_srcdir)/src/dd/cudd-2.5.0/mtr	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st -I$(top_srcdir)/src/dd/cudd-2.5.0/util		\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = cmd.hh command.hh exceptions.hh interpreter.hh typedefs.hh
PKG_CC = cmd.cc interpreter.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libcmd.la
libcmd_la_SOURCES = $(PKG_HH) $(PKG_CC)
