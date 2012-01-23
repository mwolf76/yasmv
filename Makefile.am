ACLOCAL_AMFLAGS = -I m4
SUBDIRS = src doc

PACKAGE = $(PACKAGE_NAME)
VERSION = $(PACKAGE_VERSION)

AM_CPPFLAGS = -DDATADIR=\"$(datadir)\" @CPPFLAGS@
READMES = LGPL-2.1 NEWS README

# lib_LTLIBRARIES = libgnusmv.la

# The GNUSMV test executable
# libgnusmv_la_SOURCES =
# libgnusmv_la_LIBADD = src/libavl.la
# libgnusmv__DEPENDENCIES = libgnusmv.la

# core lib for external linking:
# libavl_la_SOURCES = src/avl/avl.c
# libavl_la_LIBADD = $(top_builddir)/src/libavl.la

# lib for external linking:
# libgnusmv_la_LIBADD = $(top_builddir)/src/libavl.la
# libgnusmv_la_DEPENDENCIES = $(top_builddir)/src/libavl.la

# libgnusmvcore_la_DEPENDENCIES = $(top_builddir)/src/libavl.la

pkgconfdir = $(libdir)/pkgconfig
pkgconf_DATA = gnusmv.pc

# # ----------------------------------------------------------------------
# dist-hook:
# 	(test ! -d __tmp_gnusmv__ || rm -rf __tmp_gnusmv__)
# 	mkdir __tmp_gnusmv__
# 	mv $(distdir)/*  __tmp_gnusmv__
# 	mv __tmp_gnusmv__ $(distdir)/gnusmv
# 	mv $(CUDD_NAME) $(distdir)/
# 	$(AMTAR) cz $(externalfiles) | $(AMTAR) xz -C $(distdir) # copies external files
# 	cd $(distdir)/$(CUDD_NAME) && $(MAKE) -f $(CUDD_MAKEFILE) distclean
# #mv $(distdir)/$(minisat_gnusmv) $(distdir)
# #mv $(distdir)/$(zchaff_gnusmv) $(distdir)
# 	rm -rf `find $(distdir) -name CVS`
# 	rm -rf `find $(distdir) -name ".svn"`
# 	rm -rf `find $(distdir) -name '*~'`
# 	cd $(distdir)/gnusmv/src/parser && rm -f grammar.h grammar.c input.c
# 	cd $(distdir)/gnusmv/src/parser/ord && rm -f ord_grammar.h ord_grammar.c ord_input.c
# 	cd $(distdir)/gnusmv/src/parser/psl && rm -f psl_grammar.h psl_grammar.c psl_input.c
# 	cd $(distdir)/gnusmv/src/parser/idlist && rm -f idlist_grammar.h idlist_grammar.c idlist_input.c
# 	cd $(distdir)/gnusmv/src/addons_core/compass/parser/ap && rm -f ap_grammar.h ap_grammar.c ap_input.c
# 	cd $(distdir)/gnusmv/src/addons_core/compass/parser/prob && rm -f prob_grammar.h prob_grammar.c prob_input.c
# 	cd $(distdir)/gnusmv/src/ltl/ltl2smv && rm -f lex.c yacc.c yacc.h
# 	rm -rf $(distdir)/gnusmv/examples/TipSuite

# distcleancheck_listfiles = \
# 	find -type f -exec sh -c 'test -f $(srcdir)/{} || echo {}' ';'

# distcheck: dist
# 	$(am__remove_distdir)
# 	GZIP=$(GZIP_ENV) gunzip -c $(distdir).tar.gz | $(AMTAR) xf -
# 	chmod a+w $(distdir)
# 	mkdir $(distdir)/=build
# 	mkdir $(distdir)/=inst
# 	cp -r $(distdir)/gnusmv/helpers $(distdir)/=build
# 	cp -r $(distdir)/gnusmv/examples $(distdir)/=build

# 	dc_install_base=`$(am__cd) $(distdir)/=inst && pwd` \
# 	  && dc_src_base=`$(am__cd) $(distdir)/gnusmv && pwd` \
# 	  && $(am__cd) $(distdir)/=build \
# 	  && ../gnusmv/configure --srcdir=$(dc_src_base) --prefix=$$dc_install_base \
# 	    $(DISTCHECK_CONFIGURE_FLAGS) \
# 	  && $(MAKE) $(AM_MAKEFLAGS) \
# 	  && $(MAKE) $(AM_MAKEFLAGS) check \
# 	  && $(MAKE) $(AM_MAKEFLAGS) install \
# 	  && $(MAKE) $(AM_MAKEFLAGS) installcheck \
# 	  && $(MAKE) $(AM_MAKEFLAGS) uninstall \
# 	  && (test `find $$dc_install_base -type f -print | wc -l` -le 1 \
# 	      || { echo "ERROR: files left after uninstall:" ; \
# 	           find $$dc_install_base -type f -print ; \
# 	           exit 1; } >&2 ) \
# 	  && $(MAKE) $(AM_MAKEFLAGS) dist-gzip \
# 	  && rm -f $(distdir).tar.gz \
# 	  && $(MAKE) $(AM_MAKEFLAGS) distcleancheck
# 	$(am__remove_distdir)
# 	@echo "$(distdir).tar.gz is ready for distribution" | \
# 	  sed 'h;s/./=/g;p;x;p;x'


# # To build ps and pdf versions of the info file
# docs:
# 	cd $(top_builddir)/doc && $(MAKE) docs

# # To extract commands/helps and source code documentation
# allDocs: docs


# # The used did not build the cudd package, or the distcheck
# # target is performing its work
# if HAVE_NOT_CUDD
# CUDD_DEPENDENCY = cudd
# endif
# cudd:
# 	cd $(top_srcdir)/$(CUDD_DIR) && $(MAKE) -f $(CUDD_MAKEFILE)



# # ----------------------------------------------------------------------
# # This is for target 'distbin'
# if HAVE_ZCHAFF
# distbindir =  $(PACKAGE)-zchaff-$(VERSION)-$(host_triplet)
# else
# distbindir =  $(PACKAGE)-$(VERSION)-$(host_triplet)
# endif

# distbin: distbin_gzip

# remove_distbindir = \
#   { test ! -d $(distbindir) || { rm -fr $(distbindir); }; }

# do_distbindir:
# 	$(remove_distbindir)
# 	mkdir $(distbindir)
# 	chmod a+w $(distbindir)

# # creates the gzip distribution and strips executables
# distbin_gzip: do_distbindir
# 	$(MAKE) prefix=$(shell cd $(distbindir) && pwd) install-strip
# 	tardir=$(distbindir) && $(am__tar) | GZIP=$(GZIP_ENV) gzip -c >$(distbindir).tar.gz
# 	$(remove_distbindir)
# # ----------------------------------------------------------------------
