/*-
 * Copyright (c) 2015 UPLEX Nils Goroll Systemoptimierung
 * All rights reserved
 *
 * Author: Geoffrey Simmons <geoffrey.simmons@uplex.de>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include "config.h"

#include <stdlib.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <stdarg.h>
#include <stdio.h>

#include "vcl.h"
#include "vrt.h"
#include "vas.h"
#include "vsa.h"
#include "vtcp.h"
#include "vdef.h"
#include "vsb.h"
#include "cache/cache.h"
#include "cache/cache_director.h"
#include "cache/cache_backend.h"
#include "vapi/vsl.h"

#include "vcc_if.h"

struct bentry {
	unsigned magic;
#define BENTRY_MAGIC 0x51ced5b5
	struct director *be;
	VTAILQ_ENTRY(bentry) bentry;
};

struct belist {
	unsigned magic;
#define BELIST_MAGIC 0x66d0afdb
	VTAILQ_HEAD(behead, bentry) *behead;
};

static void
free_belist(void *priv)
{
	struct belist *belist;
	struct bentry *bentry;

	if (priv == NULL)
		return;
	CAST_OBJ(belist, priv, BELIST_MAGIC);
	AN(belist->behead);
	bentry = VTAILQ_FIRST(belist->behead);
	while (bentry != NULL) {
		struct bentry *next;

		CHECK_OBJ(bentry, BENTRY_MAGIC);
		next = VTAILQ_NEXT(bentry, bentry);
		FREE_OBJ(bentry);
		bentry = next;
	}
	FREE_OBJ(belist);
}

static void
errmsg(VRT_CTX, const char *fmt, ...)
{
	va_list args;

	va_start(args, fmt);
	if (ctx->method == VCL_MET_INIT) {
		AN(ctx->msg);
		VSB_vprintf(ctx->msg, fmt, args);
		VRT_handling(ctx, VCL_RET_FAIL);
	}
	else {
		AN(ctx->vsl);
		VSLbv(ctx->vsl, SLT_VCL_Error, fmt, args);
	}
	va_end(args);
}

static struct suckaddr *
get_suckaddr(VCL_STRING host, VCL_STRING port, int family)
{
	struct addrinfo hints, *res = NULL;
	struct suckaddr *sa = NULL;

	memset(&hints, 0, sizeof(hints));
	hints.ai_socktype = SOCK_STREAM;
	hints.ai_family = family;
	if (getaddrinfo(host, port, &hints, &res) != 0)
		return NULL;
	if (res->ai_next != NULL)
		return NULL;
	sa = VSA_Malloc(res->ai_addr, res->ai_addrlen);
	AN(sa);
	assert(VSA_Sane(sa));
	assert(VSA_Get_Proto(sa) == family);
	freeaddrinfo(res);
	return sa;
}

static char *
get_addrname(struct suckaddr *sa)
{
	char a[VTCP_ADDRBUFSIZE], p[VTCP_PORTBUFSIZE], *addr;
	struct vsb *sb = VSB_new_auto();

	VTCP_name(sa, a, sizeof(a), p, sizeof(p));
	AZ(VSB_printf(sb, "%s:%s", a, p));
	AZ(VSB_finish(sb));
	addr = strdup(VSB_data(sb));
	AN(addr);
	VSB_delete(sb);
	return(addr);
}

VCL_BOOL
vmod_create(VRT_CTX, struct vmod_priv *priv, VCL_STRING vcl_name,
	    VCL_STRING host, VCL_STRING port, VCL_PROBE probe,
	    VCL_STRING host_header, VCL_DURATION connect_timeout,
	    VCL_DURATION first_byte_timeout, VCL_DURATION between_bytes_timeout,
	    VCL_INT max_connections)
{
	struct belist *belist;
	struct bentry *bentry;
	struct director *dir;
	struct vrt_backend be = { .magic = VRT_BACKEND_MAGIC };
	struct suckaddr *sa4 = NULL, *sa6 = NULL;
	char *ipv4_addr = NULL, *ipv6_addr = NULL;
	const char *hosthdr = host_header;

	CHECK_OBJ_NOTNULL(ctx, VRT_CTX_MAGIC);
	AN(priv);
	AN(vcl_name);
	AN(host);
	AN(port);
	AN(hosthdr);

	if (vcl_name[0] == '\0') {
		errmsg(ctx, "vmod backend_dyn error: name must be non-empty");
		return 0;
	}
	if (host[0] == '\0') {
		errmsg(ctx, "vmod backend_dyn error: host must be non-empty");
		return 0;
	}
	if (hosthdr[0] == '\0')
		hosthdr = host;

	/* XXX: check that name does not already exist in ctx->vcl */

	if (priv->priv == NULL) {
		ALLOC_OBJ(belist, BELIST_MAGIC);
		AN(belist);
		belist->behead = malloc(sizeof(belist->behead));
		VTAILQ_INIT(belist->behead);
		priv->priv = belist;
		priv->free = free_belist;
	}
	else {
		CAST_OBJ(belist, priv->priv, BELIST_MAGIC);
		AN(belist->behead);
		VTAILQ_FOREACH(bentry, belist->behead, bentry) {
			CHECK_OBJ_NOTNULL(bentry, BENTRY_MAGIC);
			CHECK_OBJ_NOTNULL(bentry->be, DIRECTOR_MAGIC);
			if (strcmp(bentry->be->vcl_name, vcl_name) == 0) {
				errmsg(ctx, "Backend %s redefined", vcl_name);
				return 0;
			}
		}
	}

	sa4 = get_suckaddr(host, port, AF_INET);
	sa6 = get_suckaddr(host, port, AF_INET6);
	if (sa4 == NULL && sa6 == NULL) {
		errmsg(ctx, "vmod backend_dyn error: "
		       "Cannot resolve %s:%s as a unique IPv4 or IPv6 address",
		       host, port);
		return 0;
	}
	if (sa4 != NULL)
		ipv4_addr = get_addrname(sa4);
	if (sa6 != NULL)
		ipv6_addr = get_addrname(sa6);

	be.ipv4_suckaddr = sa4;
	be.ipv6_suckaddr = sa6;
	be.probe = probe;
#define DA(x) if (x != NULL && x[0] != '\0') be.x = strdup(x);
#define DN(x) be.x = x;
	VRT_BACKEND_HANDLE();
#undef DA
#undef DN
	if (ipv4_addr != NULL)
		free(ipv4_addr);
	if (ipv6_addr != NULL)
		free(ipv6_addr);

	dir = VRT_new_backend(ctx, &be);
	CHECK_OBJ_NOTNULL(dir, DIRECTOR_MAGIC);

	ALLOC_OBJ(bentry, BENTRY_MAGIC);
	AN(bentry);
	bentry->be = dir;
	VTAILQ_INSERT_HEAD(belist->behead, bentry, bentry);
	return 1;
}

VCL_BACKEND
vmod_by_name(VRT_CTX, struct vmod_priv *priv, VCL_STRING name)
{
	struct belist *belist;
	struct bentry *bentry;

	CHECK_OBJ_NOTNULL(ctx, VRT_CTX_MAGIC);
	AN(priv);
	AN(name);

	if (priv->priv == NULL)
		return NULL;
	CAST_OBJ_NOTNULL(belist, priv->priv, BELIST_MAGIC);
	AN(belist->behead);
	VTAILQ_FOREACH(bentry, belist->behead, bentry) {
		CHECK_OBJ_NOTNULL(bentry, BENTRY_MAGIC);
		CHECK_OBJ_NOTNULL(bentry->be, DIRECTOR_MAGIC);
		if (strcmp(name, bentry->be->vcl_name) == 0)
			return bentry->be;
	}
	return NULL;
}

VCL_BOOL
vmod_delete(VRT_CTX, struct vmod_priv *priv, VCL_BACKEND be)
{
	struct belist *belist;
	struct bentry *bentry;
	struct director *dir = NULL;

	CHECK_OBJ_NOTNULL(ctx, VRT_CTX_MAGIC);
	AN(priv);
	if (priv->priv == NULL)
		return 0;
	if (be == NULL)
		return 0;
	CHECK_OBJ(be, DIRECTOR_MAGIC);

	CAST_OBJ(belist, priv->priv, BELIST_MAGIC);
	AN(belist->behead);
	VTAILQ_FOREACH(bentry, belist->behead, bentry) {
		CHECK_OBJ_NOTNULL(bentry, BENTRY_MAGIC);
		CHECK_OBJ_NOTNULL(bentry->be, DIRECTOR_MAGIC);
		if (bentry->be == be) {
			dir = bentry->be;
			VTAILQ_REMOVE(belist->behead, bentry, bentry);
			break;
		}
	}
	if (dir == NULL)
		return 0;
	VRT_delete_backend(ctx, &dir);
	AZ(dir);
	return 1;
}

VCL_STRING
vmod_version(VRT_CTX __attribute__((unused)))
{
	return VERSION;
}
