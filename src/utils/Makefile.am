INCLUDES = -I$(top_srcdir)/src -I$(top_srcdir)/src/expr -I$(top_srcdir)/src/3rdparty/ezlogger

AM_CPPFLAGS = @AM_CPPFLAGS@
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = variant.hh
PKG_CC = variant.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libutils.la
libutils_la_SOURCES = $(PKG_SOURCES)
