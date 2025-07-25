AM_CPPFLAGS = @AM_CPPFLAGS@ -I$(top_srcdir)/src/					\
-I$(top_srcdir)/src/dd -I$(top_srcdir)/src/enc						\
-I$(top_srcdir)/src/expr -I$(top_srcdir)/src/expr/walker			\
-I$(top_srcdir)/src/type -I$(top_srcdir)/src/symb					\
-I$(top_srcdir)/src/cmd -I$(top_srcdir)/src/micro					\
-I$(top_srcdir)/src/model -I$(top_srcdir)/src/sat					\
-I$(top_srcdir)/src/algorithms -I$(top_srcdir)/src/witness			\
-I$(top_srcdir)/src/utils -I$(top_srcdir)/src/parser/grammars	    \
-I$(top_srcdir)/src/3rdparty/ezlogger								\
-I$(top_srcdir)/src/dd/cudd-2.5.0/cudd								\
-I$(top_srcdir)/src/dd/cudd-2.5.0/mtr								\
-I$(top_srcdir)/src/dd/cudd-2.5.0/st								\
-I$(top_srcdir)/src/dd/cudd-2.5.0/util								\
-I$(top_srcdir)/src/dd/cudd-2.5.0/obj

AM_CXXFLAGS = @AM_CXXFLAGS@

PKG_HH = check_init.hh check_trans.hh clear.hh commands.hh	\
diameter.hh do.hh dump_model.hh dump_trace.hh dup_trace.hh echo.hh	\
get.hh help.hh last.hh list_traces.hh load_model.hh on.hh		    \
pick_state.hh quit.hh reach.hh read_model.hh select_trace.hh		\
read_trace.hh set.hh simulate.hh time.hh

PKG_CC = check_init.cc check_trans.cc clear.cc commands.cc	\
diameter.cc do.cc dump_model.cc dump_trace.cc dup_trace.cc echo.cc	\
get.cc help.cc last.cc list_traces.cc on.cc pick_state.cc quit.cc	\
reach.cc read_model.cc read_trace.cc set.cc select_trace.cc		    \
simulate.cc time.cc

# -------------------------------------------------------

noinst_LTLIBRARIES = libcommands.la
libcommands_la_SOURCES = $(PKG_HH) $(PKG_CC)
