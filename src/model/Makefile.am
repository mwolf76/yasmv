AUTOMAKE_OPTIONS = subdir-objects
INCLUDES = -I$(top_srcdir)/src/ -I$(top_srcdir)/src/expr -I$(top_srcdir)/src/model -I$(top_srcdir)/src/mc \
-I$(top_srcdir)/src/3rdparty/ezlogger   \
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/epd	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CPPFLAGS = @AM_CPPFLAGS@
AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = cudd.hh model.hh analyzer.hh inferrer.hh encoder.hh
PKG_CC = cudd.cc model.cc analyzer.cc inferrer.cc encoder.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libmodel.la
libmodel_la_SOURCES = $(PKG_SOURCES)
