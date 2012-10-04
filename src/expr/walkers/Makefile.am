INCLUDES = -I$(top_srcdir)/src -I$(top_srcdir)/src/expr	-I$(top_srcdir)/src/model \
-I$(top_srcdir)/src/3rdparty/ezlogger   \
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/epd	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util	\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

PKG_HH = expr_walker.hh simple_expr_walker.hh temporal_expr_walker.hh	\
ltl_expr_walker.hh ctl_expr_walker.hh full_expr_walker.hh

PKG_CC = expr_walker.cc simple_expr_walker.cc temporal_expr_walker.cc	\
ltl_expr_walker.cc ctl_expr_walker.cc full_expr_walker.cc

PKG_SOURCES = $(PKG_H) $(PKG_CC)

# -------------------------------------------------------

noinst_LTLIBRARIES = libexpr_walkers.la
libexpr_walkers_la_SOURCES = $(PKG_SOURCES)
