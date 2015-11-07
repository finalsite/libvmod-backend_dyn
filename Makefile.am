ACLOCAL_AMFLAGS = -I m4 -I ${LIBVARNISHAPI_DATAROOTDIR}/aclocal

SUBDIRS = src

DISTCHECK_CONFIGURE_FLAGS = \
	VMOD_DIR='$${libdir}/varnish/vmods'

EXTRA_DIST = LICENSE

doc_DATA = LICENSE vmod_backend_dyn.3 src/vmod_backend_dyn.man.rst

dist_man_MANS = vmod_backend_dyn.3
MAINTAINERCLEANFILES = $(dist_man_MANS)

vmod_backend_dyn.3: src/vmod_backend_dyn.man.rst

%.1 %.2 %.3 %.4 %.5 %.6 %.7 %.8 %.9:
if HAVE_RST2MAN
	${RST2MAN} $< $@
else
	@echo "========================================"
	@echo "You need rst2man installed to make dist"
	@echo "========================================"
	@false
endif

