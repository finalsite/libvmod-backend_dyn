#-
# Copyright (c) 2015 UPLEX Nils Goroll Systemoptimierung
# All rights reserved
#
# Author: Geoffrey Simmons <geoffrey.simmons@uplex.de>
#
# See LICENCE
#

$Module backend_dyn 3 Varnish Module to dynamically create and delete backends

::

  import directors;

  probe p { .url = "/"; }

  sub vcl_init {
      # Backends can be created at VCL initialization.
      # The required parameters set a backend name and its host.
      # create() returns false if backend creation was unsuccessful.
      if (!backend_dyn.create(name="be1", host="be1host.com")) {
          return(fail);
      }

      # Dynamic backends may be added to directors.
      # by_name() returns the backend created with the given name.
      new rr = directors.round_robin();
      rr.add_backend(backend_dyn.by_name("be1"));

      # Backend creation supports all of the optional configuration
      # parameters available to static backend declarations; these
      # have the same default values as for a static declaration if
      # left unspecified.
      if (!backend_dyn.create(name="be1", host="be1host.com",
                              port="8080", probe=p,
			      host_header="www.mysite.com",
                              connect_timeout=1s, first_byte_timeout=2s,
                              between_bytes_timeout=3s,
                              max_connections=100)) {
          return(fail);
      }

      # Backends can also be deleted at VCL initialization.
      # delete() returns false if backend deletion was unsuccessful.
      # A deleted backend is no longer selected by any director to
      # which it was previously added.
      if (!backend_dyn.delete(backend_dyn.by_name("be1"))) {
          return(fail);
      }
  }

  sub vcl_recv {
      # Backends can be created and deleted in any VCL subroutine.
      if (req.method == "PUT") {
          if (!backend_dyn.create(name="be2", host="be2host.com")) {
              return(synth(500));
          }
          return(synth(204));
      }
      if (req.method == "DELETE") {
          if (!backend_dyn.delete(backend_dyn.by_name("be2"))) {
              return(synth(500));
          }
          return(synth(204));
      }
      set req.backend_hint = backend_dyn.by_name("be2");
  }

  sub vcl_backend_fetch {
      set bereq.backend = backend_dyn.by_name("be2");
  }

DESCRIPTION
===========

This Varnish module (VMOD) provides functions to create and delete
backends at runtime. This means that backends can be created at any
time while Varnish is running without reloading VCL, and that backends
created by the VMOD can also be deleted by the VMOD at runtime.

Backends created by the VMOD are the same as backends defined by
static declarations with the ``backend`` keyword, and they have the
same configuration parameters with the same default values. Once
created, a backend can be added to a director or assigned as a value
of ``req.backend_hint`` or ``bereq.backend``. Backends created by the
VMOD are accessed by the finder method ``by_name``, using the name
string assigned at creation.

Once deleted, a backend is no longer in use by Varnish -- it is not
selected by any director to which it may have been added, and is no
longer returned by ``by_name``.

$Function BOOL create(PRIV_VCL, STRING name, STRING host, STRING port="",
                      PROBE probe=0, STRING host_header="",
		      DURATION connect_timeout=0, DURATION first_byte_timeout=0,
                      DURATION between_bytes_timeout=0,
                      INT max_connections=0)

Description
	Create a backend with the given configuration. The parameters
	correspond to the configuration fields of a static backend
	declaration. Further restrictions on required and optional
	parameters are given below.

	``create()`` returns ``false`` if backend creation was
	unsuccessful, ``true`` on success. After successful creation,
	the backend appears in the output of the CLI command
	``backend.list``, and statistics in the ``VBE.*`` namespace
	appear in the output of ``varnishstat``. Its health can be set
	with the CLI command ``backend.set_health``.

	A backend created by the VMOD is "owned" by the VCL instance
	in which it is created, and is not available in any other VCL
	loaded by the Varnish process. The backend is deleted when its
	VCL is discarded, and it enters the cooldown state when its
	VCL is set to cold; in particular, no more health probes for
	that backend are performed, if any were defined, when the
	backend goes cold.

	The parameters may be specified as named parameters in any
	order. If used without parameter names, they MUST appear
	strictly in the order given in the function signature shown
	above.

Required Parameters
	The parameters ``name`` and ``host`` MUST be non-empty
	strings.  ``name`` MUST contain only alphanumeric characters
	or the underscore. It MAY NOT be a name already used for
	another backend created by the VMOD in the current instance of
	VCL, unless the backend with the duplicate name has been
	deleted.

	``host`` MUST be either an IP address (IPv4 or IPv6) or a host
	name that can be resolved when ``create`` is called. A host
	name may resolve to both an IPv4 and IPv6 address, but for
	each address family, it MUST resolve to exactly one address.

Optional Parameters
	``port`` MUST be a numeric port number, or a TCP service name
	listed in ``/etc/services``. The default is ``"80"``.

	``probe`` MUST specify a probe defined in a static declaration
	(or possibly a probe returned by another VMOD). If left
	unspecified, the backend has no probe.

	``host_header`` MUST be a non-empty legal value for the
	``Host`` header, and is sent as the ``Host`` header in backend
	requests. By default, the value of the ``host`` parameter is
	used for ``Host``.

	Each of ``connect_timeout``, ``first_byte_timeout`` and
	``between_bytes_timeout`` MUST be a VCL duration, such as
	``0.5s``, ``1m``, etc. If a timeout is set for a specific
	backend request (using ``bereq.connect_timeout``, etc.), then
	that timeout overrides the setting in the backend
	definition. If any of these parameters are left unspecified,
	then the timeout "hierarchy" is followed as for standard
	Varnish -- a ``bereq.*`` timeout is used if set, otherwise the
	corresponding global parameter is used (``-p
	connect_timeout``, etc.).

	``max_connections`` MUST be an integer. By default, there is
	no upper bound for the connections to a backend.

Examples::

	if (!backend_dyn.create(name="be", host="myhost.com")) {
		return(synth(500, "Backend creation failed"));
	}
	if (!backend_dyn.create(name="app", host="10.1.2.3",
                                port="8080", probe=p,
                                connect_timeout=1s, first_byte_timeout=2s,
                                between_bytes_timeout=1s)) {
		return(synth(500, "Backend creation failed"));
	}

$Function BACKEND by_name(PRIV_VCL, STRING name)

Description
	Return the backend created by the VMOD with the given name in
	the current instance of VCL. ``name`` MUST be the name of a
	backend previously created with ``create()`` in the current
	VCL.

	``by_name()`` cannot return a statically declared backend, a
	backend deleted by ``delete()``, a backend owned by another
	VCL, or a backend created by another VMOD.

	The function returns ``NULL`` if no backend with the given
	name exists (or has been deleted). If this happens when
	setting the value of ``req.backend_hint`` or ``bereq.backend``,
	the result is typically a 503 response with the FetchError
	"No backend found".

	XXX: Document dir.add_backend(NULL)

Examples::

	set req.backend_hint = backend_dyn.by_name("be");
	set bereq.backend = backend_dyn.by_name("be");
	dir.add_backend(backend_dyn.by_name("be"));
	backend_dyn.delete(backend_dyn.by_name("be"))

$Function BOOL delete(PRIV_VCL, BACKEND be)

Description
	Delete the backend created by the VMOD with the given name in
	the current instance of VCL. ``name`` MUST be the name of a
	backend previously created with ``create()`` in the current
	VCL.

	After deletion, a backend is considered unhealthy and hence is
	no longer selected for new backend requests. It enters a
	"cooldown" state of at least 60 seconds, during which it may
	complete any requests that had already begun when it was
	deleted.  Any current backend requests MUST be completed
	during this time. The ``VBE.*`` statistics for the backend
	continue to appear in the output of ``varnishstat`` during
	cooldown, and ``MAIN.n_backend`` is not decremented until
	cooldown elapses.

	The backend no longer appears in the output of
	``backend.list`` after deletion, and its health cannot be set
	by ``backend.set_health``. It is not returned by
	``by_name()``, and cannot be used to set the value of
	``req.backend_hint`` or ``bereq.backend``. If the backend had
	been previously added to a director, it is no longer selected
	by the director after deletion.

	``delete()`` cannot delete a statically declared backend, a
	backend that has already been deleted, a backend owned by
	another VCL, or a backend created by another VMOD.

	``delete()`` returns ``false`` if deletion was unsuccessful,
	``true`` otherwise.

Examples::

	if (!backend_dyn.delete(backend_dyn.by_name("be"))) {
		return(synth(500, "Backend delete failed"));
	}

$Function STRING version()

Description
	Returns the version string for this vmod.

Example::

	import std;
	std.log("Using VMOD backend_dyn version " + backend_dyn.version());

ERRORS
======

If ``create()`` is called in ``vcl_init`` and backend creation fails,
then the VCL program will fail to load, and the VCC compiler will emit
an error message.

If ``create()`` is called in any other VCL subroutine and an error
occurs, then an error message will be written to the Varnish log using
the tag ``VCL_Error``, and the function returns false.

``by_name()`` and ``delete()`` only fail if the specified backend was
not created by the VMOD in the current VCL, or if it was already
deleted. There is no error message.

REQUIREMENTS
============

This VMOD requires Varnish 4.1.0.

INSTALLATION
============

The VMOD is built against a Varnish installation, and the autotools
use ``pkg-config(1)`` to locate the necessary header files and other
resources. This sequence will install the VMOD::

  > ./autogen.sh	# for builds from the git repo
  > ./configure
  > make
  > make check		# to run unit tests in src/tests/*.vtc
  > make distcheck	# run check and prepare a distribution tarball
  > sudo make install

If you have installed Varnish in a non-standard directory, call
``autogen.sh`` and ``configure`` with the ``PKG_CONFIG_PATH``
environment variable pointing to the appropriate path. For example,
when varnishd configure was called with ``--prefix=$PREFIX``, use::

  > PKG_CONFIG_PATH=${PREFIX}/lib/pkgconfig
  > export PKG_CONFIG_PATH

By default, the vmod ``configure`` script installs the vmod in
the same directory as Varnish, determined via ``pkg-config(1)``. The
vmod installation directory can be overridden by passing the
``VMOD_DIR`` variable to ``configure``.

Other files such as this man-page are installed in the locations
determined by ``configure``, which inherits its default ``--prefix``
setting from Varnish.

For developers
--------------

As with Varnish, you can use these ``configure`` options for developer
builds:

*  ``--enable-developer-warnings``

   * Set stricter error and warning levels for compilation. The VMOD
     MUST always build successfully with this option enabled.

* ``--enable-debugging-symbols``

   * Make the VMOD's symbols available to debuggers, core dumps and so forth.

* ``--enable-stack-protector``

   * Emit extra code to avoid buffer overflows

See ``configure --help`` for a full list of configuration options and
environment variables.

AUTHOR
======

* Geoffrey Simmons <geoff@uplex.de>

UPLEX Nils Goroll Systemoptimierung

LIMITATIONS
===========

``create()`` prevents the use of duplicate backend names created by
this VMOD in the current instance of VCL, but it cannot prevent the
re-use of a backend name created by other means, for example by a
static declaration or another VMOD. Varnish has no problem using
backends with duplicate names, since they are represented internally
as distinct objects. But if two backends have the same name, they
appear as duplicate entries in the output of ``backend.list``; and if
one of them is sick while the other is healthy, it is impossible to
tell which is which. Also, ``VBE.*`` stats are maintained for only one
of the backends with that name. So you should take care not to create
backends with names used elsewhere in the VCL.

``by_name()`` searches for backends in a linear list, and is locked
out of the search if ``create()`` or ``delete()`` are executing
concurrently. If you have a large number of dynamic backends, it
is probably more efficient to add them to directors (even a director
that has only one backend) than to set ``req.backend_hint`` or
``bereq.backend`` using ``by_name()``, since a director does not
execute the linear search.

It is in the nature of dynamic backends that they are not preserved
when Varnish stops or when the VCL is discarded. While dynamic
backends make it possible to change the backend configuration without
reloading VCL, you may nevertheless want to update your backend
configuration in VCL sources on the file system, so that your backends
are not "lost" on restart.

SEE ALSO
========

* varnishd(1)
* vcl(7)
* `"Writing a Director" <https://www.varnish-cache.org/docs/4.1/reference/directors.html/>`_

COPYRIGHT
=========

This document is licensed under the same conditions as the
libvmod-backend_dyn project. See LICENSE for details.

* Copyright (c) 2015 UPLEX Nils Goroll Systemoptimierung
