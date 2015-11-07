AM_CPPFLAGS = @VMOD_INCLUDES@ -Wall -Werror

vmoddir = @VMOD_DIR@
vmod_LTLIBRARIES = libvmod_backend_dyn.la

libvmod_backend_dyn_la_LDFLAGS = -module -export-dynamic -avoid-version -shared

libvmod_backend_dyn_la_SOURCES = \
	vmod.c

nodist_libvmod_backend_dyn_la_SOURCES = \
	vcc_if.c \
	vcc_if.h

vmod.lo: vcc_if.c vcc_if.h

vcc_if.c: vcc_if.h

vcc_if.h: @VMODTOOL@ $(top_srcdir)/src/vmod.vcc
	@VMODTOOL@ $(top_srcdir)/src/vmod.vcc

VMOD_TESTS = $(top_srcdir)/src/tests/*.vtc
.PHONY: $(VMOD_TESTS)

$(top_srcdir)/src/tests/*.vtc: libvmod_backend_dyn.la
	@VARNISHTEST@ -Dvarnishd=@VARNISHD@ -Dvmod_topbuild=$(abs_top_builddir) $@

check: $(VMOD_TESTS)

EXTRA_DIST = \
	vmod.vcc \
	$(VMOD_TESTS)

CLEANFILES = \
	$(builddir)/vcc_if.c \
	$(builddir)/vcc_if.h \
	$(builddir)/vmod_backend_dyn.rst \
	$(builddir)/vmod_backend_dyn.man.rst
