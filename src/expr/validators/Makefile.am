INCLUDES = -I$(top_srcdir)/src -I$(top_srcdir)/src/expr -I$(top_srcdir)/src/3rdparty/ezlogger

PKG_HH = expr_validator.hh
PKG_CC = expr_validator.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libexpr_validators.la
libexpr_validators_la_SOURCES = $(PKG_SOURCES)
