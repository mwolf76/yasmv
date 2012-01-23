AUTOMAKE_OPTIONS = subdir-objects
INCLUDES = -I$(top_srcdir)/src/ -I$(top_srcdir)/src/expr -I$(top_srcdir)/src/model -I$(top_srcdir)/src/3rdparty/ezlogger

PKG_HH = model.hh
PKG_CC = model.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libmodel.la
libmodel_la_SOURCES = $(PKG_SOURCES)
