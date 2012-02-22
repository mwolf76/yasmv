AUTOMAKE_OPTIONS = subdir-objects
SUBDIRS = printers validators
INCLUDES = -I$(top_srcdir)/src -I$(top_srcdir)/src/mc -I$(top_srcdir)/src/3rdparty/ezlogger

PKG_HH = mc.hh mc_walker.hh
PKG_CC = mc.cc mc_walker.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libmc.la
libmc_la_SOURCES = $(PKG_SOURCES)
