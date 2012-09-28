AUTOMAKE_OPTIONS = subdir-objects
INCLUDES = -I$(top_srcdir)/src/ -I$(top_srcdir)/src/expr -I$(top_srcdir)/src/command -I$(top_srcdir)/src/mc \
-I$(top_srcdir)/src/3rdparty/ezlogger   \
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/epd	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CPPFLAGS = @AM_CPPFLAGS@
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = command.hh
PKG_CC = command.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libcommand.la
libcommand_la_SOURCES = $(PKG_SOURCES)
