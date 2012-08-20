AUTOMAKE_OPTIONS = subdir-objects

INCLUDES = -I$(top_srcdir)/src -I$(top_srcdir)/src/mc -I$(top_srcdir)/src/expr -I$(top_srcdir)/src/model -I$(top_srcdir)/src/3rdparty/ezlogger

AM_CPPFLAGS=@AM_CPPFLAGS@
AM_CXXFLAGS=@AM_CXXFLAGS@

PKG_HH = mc.hh satbmc.hh isatbmc.hh
PKG_CC = mc.cc satbmc.cc isatbmc.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libmc.la
libmc_la_SOURCES = $(PKG_SOURCES)
