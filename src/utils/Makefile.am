AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src

AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = clock.hh misc.hh pool.hh time.hh values.hh variant.hh
PKG_CC = clock.cc misc.cc variant.cc pool.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libutils.la
libutils_la_SOURCES = $(PKG_HH) $(PKG_CC)
