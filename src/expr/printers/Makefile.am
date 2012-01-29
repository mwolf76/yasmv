INCLUDES = -I$(top_srcdir)/src -I$(top_srcdir)/src/expr -I$(top_srcdir)/src/3rdparty/ezlogger

PKG_HH = expr_printer.hh
PKG_CC = expr_printer.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libexpr_printers.la
libexpr_printers_la_SOURCES = $(PKG_SOURCES)
