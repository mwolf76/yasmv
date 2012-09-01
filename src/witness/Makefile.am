AUTOMAKE_OPTIONS = subdir-objects
INCLUDES = -I$(top_srcdir)/src/ -I$(top_srcdir)/src/expr -I$(top_srcdir)/src/witness -I$(top_srcdir)/src/3rdparty/ezlogger

AM_CPPFLAGS = @AM_CPPFLAGS@
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = witness.hh
PKG_CC = witness.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libwitness.la
libwitness_la_SOURCES = $(PKG_SOURCES)
