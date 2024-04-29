## $Id$
## DDD Makefile template.
## Process this file with `automake' to produce a `Makefile.in'.

# $Id$
# DDD top-level Makefile.

# Copyright (C) 2000 Universitaet Passau, Germany.
# Copyright (C) 2001 Universitaet des Saarlandes, Germany.
# Written by Andreas Zeller <zeller@gnu.org>.
# 
# This file is part of DDD.
# 
# DDD is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public
# License as published by the Free Software Foundation; either
# version 3 of the License, or (at your option) any later version.
# 
# DDD is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
# See the GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public
# License along with DDD -- see the file COPYING.
# If not, see <http://www.gnu.org/licenses/>.
# 
# DDD is the data display debugger.
# For details, see the DDD World-Wide-Web page, 
# `http://www.gnu.org/software/ddd/',
# or send a mail to the DDD developers <ddd@gnu.org>.

ACLOCAL_AMFLAGS = -I m4

TEXINFO_DISTFILES = \
	texinfo/epsf.tex texinfo/gfdl.texinfo texinfo/gpl.texinfo \
	texinfo/lgpl.texinfo texinfo/texinfo.tex ddd/PICS

# Shared data installation
dddrootdir   = $(pkgdatadir)-$(VERSION)

# -----------------------------------------------------------------------------
# Subdirectories.
# -----------------------------------------------------------------------------

SUBDIRS = themes vsllib ddd


# -----------------------------------------------------------------------------
# Tools.
# -----------------------------------------------------------------------------

TAR  = @TAR@
GZIP = gzip
SED  = sed


# -----------------------------------------------------------------------------
# Distribution (via etc/make-final).
# -----------------------------------------------------------------------------

# The build number.  (This must be set from outside)
REL = 1

# -----------------------------------------------------------------------------
# Autoconf.
# -----------------------------------------------------------------------------

EXTRA_DIST = \
	$(srcdir)/etc \
	$(TEXINFO_DISTFILES) \
        doc/CREDITS doc/NEWS doc/FONTS doc/NICKNAMES

dist-hook:
	rm -rf `find $(distdir)/ddd/PICS -name CVS -o -name .cvsignore -o -name \*.jpg -o -name \*.pdf -o -name .svn`

# -----------------------------------------------------------------------------
# Documentation targets
# -----------------------------------------------------------------------------
.PHONY: html pdf 
html:
	cd ddd && $(MAKE) html

pdf:
	cd ddd && $(MAKE) pdf
