AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = walker printer

AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_CC = atom.cc expr.cc timed_expr.cc pool.cc expr_mgr.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libexpr.la
libexpr_la_SOURCES = $(PKG_CC)
