AUTOMAKE_OPTIONS = subdir-objects
INCLUDES = -I$(top_srcdir)/src/ -I$(top_srcdir)/src/expr -I$(top_srcdir)/src/trace -I$(top_srcdir)/src/3rdparty/ezlogger

AM_CPPFLAGS = @AM_CPPFLAGS@
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = trace.hh
PKG_CC = trace.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libtrace.la
libtrace_la_SOURCES = $(PKG_SOURCES)
