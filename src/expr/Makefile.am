AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = compilers printers validators
INCLUDES = -I$(top_srcdir)/src -I$(top_srcdir)/src/expr -I$(top_srcdir)/src/3rdparty/ezlogger

AM_CPPFLAGS = @AM_CPPFLAGS@
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = expr.hh expr_walker.hh variant.hh
PKG_CC = expr.cc expr_walker.cc variant.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libexpr.la
libexpr_la_SOURCES = $(PKG_SOURCES)
