## $Id$
## DDD Makefile template.
## Process this file with `automake' to produce a `Makefile.in'.

# $Id$
# DDD Makefile.

# Copyright (C) 2000-2001 Universitaet Passau, Germany.
# Written by Andreas Zeller <zeller@gnu.org>.
#
# Copyright (C) 2001-2004, 2006 Free Software Foundation, USA.
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

# -----------------------------------------------------------------------------
# General Settings.
# -----------------------------------------------------------------------------

# Various utilities.
CAT  = cat
MV   = mv
ECHO = echo
GREP = grep
DATE = date
CMP  = cmp
RM   = rm -f

# Suffixes used in this file.
SUFFIXES = .C .c .Y .L .txt .xbm .xbmxx .xpm .xpmxx \
	   .xface .fig .jpg .png .gif .pdf $(IMGEXT)

# Shared data installation
dddrootdir    = $(pkgdatadir)-@VERSION@
dddappdir     = $(pkgdatadir)-@VERSION@/@ddd@
desktopdir    = $(datadir)/applications
ddddocdir     = $(dddrootdir)/doc
infodir       = $(dddrootdir)/info
mandir        = $(dddrootdir)/man


# -----------------------------------------------------------------------------
# DDD Sources.
# -----------------------------------------------------------------------------

# General-purpose utilities: strings, regexps, run-type type info...
BASE_SRC = \
	base/assert.h     \
	base/assert.C     \
	base/attribute.h  \
	base/basename.C   \
	base/basename.h   \
	base/bool.h       \
	base/casts.h      \
	base/compare.C    \
	base/compare.h    \
	base/cook.C       \
	base/cook.h       \
	base/cwd.C        \
	base/cwd.h        \
	base/explicit.h   \
	base/getrlimit.h  \
	base/glob.C       \
	base/glob.h       \
	base/hash.C       \
	base/hash.h       \
	base/home.C       \
	base/home.h       \
	base/hypot.h      \
	base/isid.C       \
	base/isid.h       \
	base/misc.h       \
	base/mutable.h    \
	base/my-alloca.h  \
	base/my-dirent.h  \
	base/oldcxx.h     \
	base/pi.h         \
	base/rxclass.C    \
	base/rxclass.h    \
	base/sigName.C    \
	base/sigName.h    \
	base/strclass.C   \
	base/strclass.h   \
	base/streampos.h  \
	base/strtoul.h    \
	base/tabs.C       \
	base/tabs.h       \
	base/uniquify.C   \
	base/uniquify.h   \
	base/Logger.C     \
	base/Logger.h     \
	base/MemCheck.C   \
	base/MemCheck.h   \
	base/MemCheckD.h  \
	base/PrintGC.C    \
	base/PrintGC.h    \
	base/SignalB.C    \
	base/SignalB.h    \
	base/TypeInfo.C   \
	base/TypeInfo.h   \
	base/UniqueId.C   \
	base/UniqueId.h

# Instantiated templates
TEMPLATE_SRC = \
	template/Assoc.h      \
	template/IntIntAA.h   \
	template/Map.h        \
	template/Queue.h      \
	template/StatArray.h  \
	template/StringSA.h   \
	template/VoidArray.h  \
	template/WidgetSA.h

# Interprocess communication
# Top-level class is `Agent', declared in `Agent.h'
AGENT_SRC = \
	agent/Agent.C      \
	agent/Agent.h      \
	agent/AgentM.C     \
	agent/AgentM.h     \
	agent/AsyncAgent.C \
	agent/AsyncAgent.h \
	agent/ChunkQueue.C \
	agent/ChunkQueue.h \
	agent/DataLength.C \
	agent/DataLength.h \
	agent/HandlerL.C   \
	agent/HandlerL.h   \
	agent/LiterateA.C  \
	agent/LiterateA.h  \
	agent/ReadLineA.C  \
	agent/ReadLineA.h  \
	agent/TimeOut.C    \
	agent/TimeOut.h    \
	agent/TTYAgent.C   \
	agent/TTYAgent.h

# Miscellaneous utilities for X programs: Motif strings, hourglasses,
# context-sensitive help...
XSTUFF_SRC = \
	x11/charsets.C   \
	x11/charsets.h   \
	x11/converters.C \
	x11/converters.h \
	x11/events.C     \
	x11/events.h     \
	x11/findParent.C \
	x11/findParent.h \
	x11/findWindow.C \
	x11/findWindow.h \
	x11/fileSBF.C    \
	x11/fileSBF.h    \
	x11/frame.C      \
	x11/frame.h      \
	x11/longName.C   \
	x11/longName.h   \
	x11/selection.C  \
	x11/selection.h  \
	x11/verify.C     \
	x11/verify.h     \
	x11/AutoRaise.C  \
	x11/AutoRaise.h  \
	x11/Delay.C      \
	x11/Delay.h      \
	x11/DeleteWCB.C  \
	x11/DeleteWCB.h  \
	x11/DestroyCB.C  \
	x11/DestroyCB.h  \
	x11/ExitCB.C     \
	x11/ExitCB.h     \
	x11/InitImage.C  \
	x11/InitImage.h  \
	x11/OnOff.h      \
	x11/Sash.h       \
	x11/Swallower.C  \
	x11/Swallower.h  \
	x11/SwallowerP.h \
	x11/Widget.h     \
	x11/Xpm.h        \
	x11/XErrorB.C    \
	x11/XErrorB.h

# Same, but for Motif
MSTUFF_SRC = \
	motif/freeXmST.C   \
	motif/freeXmST.h   \
	motif/MakeMenu.C   \
	motif/MakeMenu.h   \
	motif/MString.C    \
	motif/MString.h    \
	motif/ComboBox.C   \
	motif/ComboBox.h   \
	motif/SpinBox.C    \
	motif/SpinBox.h    \
	motif/TextSetS.C   \
	motif/TextSetS.h

# Box library - rectangular composible graphical items
# Top-level class is `Box', declared in `Box.h'
BOX_SRC = \
	box/printBox.C   \
	box/printBox.h   \
	box/AlignBox.C   \
	box/AlignBox.h   \
	box/ArcBox.C     \
	box/ArcBox.h     \
	box/BinBox.C     \
	box/BinBox.h     \
	box/Box.C        \
	box/Box.h        \
	box/BoxC.h       \
	box/BoxD.C       \
	box/BoxD.h       \
	box/BoxExtend.C  \
	box/BoxExtend.h  \
	box/BoxPoint.C   \
	box/BoxPoint.h   \
	box/BoxRegion.C  \
	box/BoxRegion.h  \
	box/BoxSize.C    \
	box/BoxSize.h    \
	box/BoxWeight.h  \
	box/ColorBox.C   \
	box/ColorBox.h   \
	box/CompositeB.C \
	box/CompositeB.h \
	box/DataLink.h   \
	box/DiagBox.C    \
	box/DiagBox.h    \
	box/DummyBox.C   \
	box/DummyBox.h   \
	box/FixBox.C     \
	box/FixBox.h     \
	box/FontFixBox.C \
	box/FontFixBox.h \
	box/FontTable.C  \
	box/FontTable.h  \
	box/HatBox.C     \
	box/HatBox.h     \
	box/LineBox.C    \
	box/LineBox.h    \
	box/ListBox.C    \
	box/ListBox.h    \
	box/MarkBox.C    \
	box/MarkBox.h    \
	box/MatchBox.C   \
	box/MatchBox.h   \
	box/PrimitiveB.C \
	box/PrimitiveB.h \
	box/SlopeBox.C   \
	box/SlopeBox.h   \
	box/StringBox.C  \
	box/StringBox.h  \
	box/THatBox.C    \
	box/THatBox.h    \
	box/TagBox.C     \
	box/TagBox.h     \
	box/TrueBox.C    \
	box/TrueBox.h

# VSL library - building boxes from structured data
# Top-level class is `VSLLib', declared in `VSLLib.h'
VSL_SRC = \
	vslsrc/ArgNode.C    \
	vslsrc/ArgNode.h    \
	vslsrc/BuiltinCN.C  \
	vslsrc/BuiltinCN.h  \
	vslsrc/CallNode.C   \
	vslsrc/CallNode.h   \
	vslsrc/ConstNode.C  \
	vslsrc/ConstNode.h  \
	vslsrc/DefCallN.C   \
	vslsrc/DefCallN.h   \
	vslsrc/DummyNode.C  \
	vslsrc/DummyNode.h  \
	vslsrc/LetNode.C    \
	vslsrc/LetNode.h    \
	vslsrc/NameNode.C   \
	vslsrc/NameNode.h   \
	vslsrc/ListNode.C   \
	vslsrc/ListNode.h   \
	vslsrc/TestNode.C   \
	vslsrc/TestNode.h   \
	vslsrc/ThemeVSLL.C  \
	vslsrc/ThemeVSLL.h  \
	vslsrc/TrueNode.C   \
	vslsrc/TrueNode.h   \
	vslsrc/VSEFlags.C   \
	vslsrc/VSEFlags.h   \
	vslsrc/VSLArgList.C \
	vslsrc/VSLArgList.h \
	vslsrc/VSLBuiltin.C \
	vslsrc/VSLBuiltin.h \
	vslsrc/VSLDef.C     \
	vslsrc/VSLDef.h     \
	vslsrc/VSLDefList.C \
	vslsrc/VSLDefList.h \
        vslsrc/VSLErr.C     \
	vslsrc/VSLLib.C     \
	vslsrc/VSLLib.h     \
	vslsrc/VSLNode.C    \
	vslsrc/VSLNode.h    \
        vslsrc/VSLRead.C

# Graph structure, graph layout and graph editor widget
# Top-level classes are `Graph', declared in `Graph.h'
# and the `GraphEdit' widget, declared in `GraphEdit.h'.
GRAPH_SRC = \
	graph/ArcGraphE.C  \
	graph/ArcGraphE.h  \
	graph/BoxEdgeA.C   \
	graph/BoxEdgeA.h   \
	graph/BoxGraphN.C  \
	graph/BoxGraphN.h  \
	graph/EdgeA.C      \
	graph/EdgeA.h      \
	graph/EdgeAPA.h    \
	graph/Graph.C      \
	graph/Graph.h      \
	graph/GraphEdge.C  \
	graph/GraphEdge.h  \
	graph/GraphEdit.C  \
	graph/GraphEdit.h  \
	graph/GraphEditP.h \
	graph/GraphGC.C    \
	graph/GraphGC.h    \
	graph/GraphNode.C  \
	graph/GraphNode.h  \
	graph/GraphNodeI.h \
	graph/GraphNPA.h   \
	graph/HintGraphN.C \
	graph/HintGraphN.h \
	graph/LineGraphE.C \
	graph/LineGraphE.h \
	graph/LineGESI.C   \
	graph/LineGESI.h   \
	graph/PannedGE.C   \
	graph/PannedGE.h   \
	graph/PannedGEP.h  \
	graph/PosGraphN.C  \
	graph/PosGraphN.h  \
	graph/RegionGN.C   \
	graph/RegionGN.h   \
	graph/ScrolledGE.C \
	graph/ScrolledGE.h \
	graph/ScrolleGEP.h \
	graph/layout.C     \
	graph/layout.h

# The DDD application itself.  `ddd.C' is the main program, `SourceView.C'
# is the source window, `DataDisp.C' is the data window.
DDD_SRC = \
	ddd.h \
	eps-code.h   \
	annotation.C \
	annotation.h \
	args.C       \
	args.h       \
	buttons.C    \
	buttons.h    \
	cmdtty.C     \
	cmdtty.h     \
	comm-manag.C \
	comm-manag.h \
	complete.C   \
	complete.h   \
	ctrl.C       \
	ctrl.h       \
	data.C       \
	data.h       \
	darkmode.C \
	darkmode.h \
	dbx-lookup.C \
	dbx-lookup.h \
	decoration.C \
	decoration.h \
	deref.C      \
	deref.h      \
	disp-read.C  \
	disp-read.h  \
	editing.C    \
	editing.h    \
	environ.C    \
	environ.h    \
	examine.C    \
	examine.h    \
	exectty.C    \
	exectty.h    \
	exit.C       \
	exit.h       \
	expired.C    \
	expired.h    \
	file.C       \
	file.h       \
	filetype.C   \
	filetype.h   \
	fonts.C      \
	fonts.h      \
	fortranize.C \
	fortranize.h \
	gdbinit.C    \
	gdbinit.h    \
	history.C    \
	history.h    \
	hostname.C   \
	hostname.h   \
	index.C      \
	index.h      \
	java.C 	     \
	java.h 	     \
	logo.C       \
	logo.h       \
	logplayer.C  \
	logplayer.h  \
	mainloop.C   \
	mainloop.h   \
	mydialogs.C  \
	mydialogs.h  \
	options.C    \
	options.h    \
	plotter.C    \
	plotter.h    \
	post.C       \
	post.h       \
	print.C      \
	print.h      \
	question.C   \
	question.h   \
	regexps.C    \
	regexps.h    \
	resolveP.C   \
	resolveP.h   \
	resources.C  \
	resources.h  \
	sashes.C     \
	sashes.h     \
	select.C     \
	select.h     \
	session.C    \
	session.h    \
	settings.C   \
	settings.h   \
	shell.C      \
	shell.h      \
	shorten.C    \
	shorten.h    \
	show.C       \
	show.h       \
	simpleMenu.C \
	simpleMenu.h \
	source.C     \
	source.h     \
	status.C     \
	status.h     \
	string-fun.C \
	string-fun.h \
	stty.h       \
	tempfile.h   \
	tempfile.C   \
	tictactoe.C  \
	tictactoe.h  \
	tips.C       \
	tips.h       \
	toolbar.C    \
	toolbar.h    \
	ungrab.C     \
	ungrab.h     \
	value-read.C \
	value-read.h \
	vsldoc.C     \
	vsldoc.h     \
	windows.C    \
	windows.h    \
	wm.C         \
	wm.h         \
	xconfig.C    \
	xconfig.h    \
	AliasGE.C    \
	AliasGE.h    \
	AppData.h    \
	ArgField.C   \
	ArgField.h   \
	BindingS.h   \
	BreakPoint.C \
	BreakPoint.h \
	CodeCache.C  \
	CodeCache.h  \
	Command.C    \
	Command.h    \
	DataDisp.C   \
	DataDisp.h   \
	DispBox.C    \
	DispBox.h    \
	DispBuffer.C \
	DispBuffer.h \
	DispGraph.C  \
	DispGraph.h  \
	DispNode.C   \
	DispNode.h   \
	DispValue.C  \
	DispValue.h  \
	DispValueT.C \
	DispValueT.h \
	EntryType.h  \
	GDBAgent.C   \
	GDBAgent.h   \
	GDBAgent_BASH.C \
	GDBAgent_BASH.h \
	GDBAgent_DBG.C \
	GDBAgent_DBG.h \
	GDBAgent_DBX.C \
	GDBAgent_DBX.h \
	GDBAgent_GDB.C \
	GDBAgent_GDB.h \
	GDBAgent_JDB.C \
	GDBAgent_JDB.h \
	GDBAgent_MAKE.C \
	GDBAgent_MAKE.h \
	GDBAgent_PERL.C \
	GDBAgent_PERL.h \
	GDBAgent_PYDB.C \
	GDBAgent_PYDB.h \
	GDBAgent_XDB.C \
	GDBAgent_XDB.h \
	HelpCB.C     \
	HelpCB.h     \
	HistoryD.C   \
	HistoryD.h   \
	HistoryF.h   \
	IntArray.h   \
	MinMaxA.h    \
	PlotAgent.C  \
	PlotAgent.h  \
	PlotArea.C   \
	PlotArea.h   \
	PosBuffer.C  \
	PosBuffer.h  \
	ProgressM.C  \
	ProgressM.h  \
	RefreshDI.C  \
	RefreshDI.h  \
	SmartC.C     \
	SmartC.h     \
	SourceCode.C \
	SourceCode.h \
	SourceView.C \
	SourceView.h \
	StringTPA.h  \
	ThemeM.C     \
	ThemeM.h     \
	ThemeP.C     \
	ThemeP.h     \
	Tool.C       \
	Tool.h       \
	UndoBuffer.C \
	UndoBuffer.h \
	UndoBE.C     \
	UndoBE.h     \
	WhatNextCB.C \
	WhatNextCB.h

# part of the athena library modified for DDD
ATHENA_SRC = \
	athena_ddd/PannerM.C \
	athena_ddd/PannerM.h \
	athena_ddd/PannerMP.h 

# Make sure needed headers are built before they are used
BUILT_SOURCES = \
	build.h      \
	host.h       \
	root.h       \
	version.h    \
	Ddd.ad.h     \
	ddd.vsl.h

# -----------------------------------------------------------------------------
# Local Libraries.
# -----------------------------------------------------------------------------

# POSIX regex routines (from system)
# LIBRX      = @LIBRX@
LIBRX      =
# termcap routines (from system)
LIBTERMCAP = @LIBTERMCAP@
# -lreadline library (from system)
LIBREADLINE = @LIBREADLINE@
# Yacc library (-ly)
LIBY       = @LIBY@
# Math library (-lm)
LIBM       = @LIBM@
# C library (-lc)
LIBC       = @LIBC@
# Socket library (-lsocket)
#LIBSOCKET  = @LIBSOCKET@
LIBSOCKET  = 
# ELF library (-lelf)
LIBELF     = @LIBELF@
# NSL library (-lnsl)
LIBNSL     = @LIBNSL@
# Additional libraries required for non-X programs (-lsocket -lnsl)
NON_X_LIBS = @LIBS@

# All libraries shown above
ALL_LIBS = $(CXXLIBS) $(LIBREADLINE) $(LIBSOCKET) $(LIBNSL) $(LIBRX) \
	$(LIBTERMCAP) $(LIBY) $(LIBM) $(LIBELF)



# -----------------------------------------------------------------------------
# X Libraries.
# -----------------------------------------------------------------------------

# Special flags for linking with X.  (-L/usr/X11R5/lib)
X_LDFLAGS = @X_LIBS@

# Special flags to set the run-time library search path.
RPATH = @RPATH@

# Motif library.  (-lXm)
LIBXM = @XM_LIBS@

# Use this alternative for building `semistatic' executables
# where Motif libraries are statically linked in.
# LIBXM = -Wl,-Bstatic @XM_LIBS@ -Wl,-Bdynamic
# Libtool has a bug and moves -Wl,xxx before any other link flags.
# The following workaround should work:
# LIBXM = -Wl,$(X_LDFLAGS) -Wl,-Bstatic -Wl,@XM_LIBS@ -Wl,-Bdynamic
# Alternatively, just define (with the proper path)
# LIBXM = /path/to/libXm.a
# This can be done interactively: "make LIBXM=/path/to/libXm.a"

# Athena libraries.  (-lXaw)
LIBXAW = @XAW_LIBS@

# Freetype2 libraries
LIBXFT = @XFT_LIBS@ -lfontconfig

# Freetype2 headers
XFTINCLUDE = @XFT_INCLUDE@

# X Miscellaneous  Utilities needed for Athena and Motif >= 2.0 (lXmu)
LIBXMU = @XMU_LIBS@

# X extension library; needed for Athena and Motif >= 2.0.  (-lXext)
LIBXEXT = @XEXT_LIBS@

# Xpm pixmap library; needed for DDD and sometimes for Motif >= 2.0.  (-lXpm)
LIBXPM = @XPM_LIBS@

# Xp printing extension library; sometimes needed for Motif >= 2.1.  (-lXp)
LIBXP = @XP_LIBS@

# gen library; sometimes needed for Motif >= 2.0.  (-lgen)
LIBGEN = @LIBGEN@

# X toolkit library.  (-lXt)
LIBXT = @XT_LIBS@

# X library.  (-lX11 -lSM -lICE -lnsl -lsocket)
# libSM: Session Management extension
# libICE: Inter-Client Exchange extension
LIBX11 = @X_PRE_LIBS@ @X11_LIBS@ @X_EXTRA_LIBS@

# All libraries shown above
ALL_X_LIBS = $(X_LDFLAGS) $(LIBXM) $(LIBXAW) $(LIBXMU) $(LIBXT) $(LIBXPM) \
             $(LIBXP) $(LIBXEXT) $(LIBX11) $(LIBXFT) $(LIBGEN)


# -----------------------------------------------------------------------------
# Building DDD (and others).
# -----------------------------------------------------------------------------

# The flags we use to compile C++ files.
# Optimizing flags. (-DNDEBUG -O2)
CXXOPT = @CXXOPT@
# Debugging flags.  (-g)
CXXDEBUG = @CXXDEBUG@
# Warnings.  (-W -Wall)
CXXWARNINGS = @CXXWARNINGS@
# Extras.  (-trigraphs)
CXXSTUFF = @CXXSTUFF@ @X_PERMISSIVE@
CXXFLAGS = $(CXXOPT) $(CXXDEBUG) $(CXXWARNINGS) $(CXXSTUFF)

bin_PROGRAMS = ddd

noinst_PROGRAMS = stringify ctest cxxtest vsl
ddd_SOURCES = ddd.C \
	$(BASE_SRC) \
	$(TEMPLATE_SRC) \
	$(AGENT_SRC) \
	$(XSTUFF_SRC) \
	$(MSTUFF_SRC) \
	$(BOX_SRC) \
	$(VSL_SRC) \
	$(GRAPH_SRC) \
	$(DDD_SRC) \
	$(ATHENA_SRC)

stringify_SOURCES = stringify.C
STRINGIFY = ./stringify$(EXEEXT)
ctest_SOURCES     = ctest.c
cxxtest_SOURCES   = cxxtest.C
vsl_SOURCES       = vsl.C \
	DocSpace.c \
	DocSpace.h \
	DocSpaceP.h \
	string-fun.C \
	regexps.C \
	darkmode.C \
	$(BASE_SRC) \
	$(TEMPLATE_SRC) \
	$(AGENT_SRC) \
	$(XSTUFF_SRC) \
	$(MSTUFF_SRC) \
	$(BOX_SRC) \
	$(VSL_SRC)

vsl_CFLAGS = @CFLAGS@
vsl_CFLAGS += @MINIMAL_TOC@

cxxtest_LDADD = $(LIBM)
ddd_LDADD = $(RPATH) $(ALL_X_LIBS) $(ALL_LIBS)
vsl_LDADD = $(RPATH) $(ALL_X_LIBS) $(ALL_LIBS)
X_INCLUDE = @X_CFLAGS@
AM_CPPFLAGS = -I$(srcdir)/.. -I.. $(X_INCLUDE) $(XFTINCLUDE)

# -----------------------------------------------------------------------------
# DDD Application Defaults.
# -----------------------------------------------------------------------------

# The resource header and app-default files.

Ddd.ad.h: x11/Ddd $(srcdir)/ad2c.sed
	$(CAT) x11/Ddd | $(DELETE_CR) | \
	$(SED) -n -f $(srcdir)/ad2c.sed > $@~ && $(MV) $@~ $@

$(srcdir)/x11/Ddd.in: $(srcdir)/../m4/Ddd.in.m4 $(srcdir)/../m4/tips.m4 \
	$(srcdir)/../m4/macros.m4 $(srcdir)/../m4/colors.m4 
	$(M4) -D srcdir=$(srcdir) $(srcdir)/../m4/Ddd.in.m4 $(srcdir)/../m4/tips.m4 \
	  | $(DELETE_CR) > $@

$(srcdir)/../m4/tips.m4: $(srcdir)/../doc/TIPS $(srcdir)/tips2m4.awk
	$(AWK) -f $(srcdir)/tips2m4.awk $(srcdir)/../doc/TIPS | $(DELETE_CR) \
	    > $@~ && $(MV) $@~ $@

$(top_builddir)/ddd/tips.html: $(srcdir)/../doc/TIPS
	$(M4) -D srcdir=$(srcdir) -D macros=$(srcdir)/../m4/html.m4 $(srcdir)/../doc/TIPS \
	  | $(AWK) -f $(srcdir)/tips2html.awk | \
	$(SED) 's/\\133/\[/g' | $(SED) 's/\\135/\]/g' | \
	$(SED) 's/@\([A-Z][A-Z]*\)@/\1/g' | $(SED) 's/@ /@/g' \
	| $(DELETE_CR) > $@

# -----------------------------------------------------------------------------
# VSL.
# -----------------------------------------------------------------------------

# The VSL header files.

vsldir  = $(srcdir)/../vsllib

VSL_CPP = $(CPP) -I$(vsldir) -I$(prefix)/lib/vsl-include

VSLSRC = \
	$(vsldir)/std.vsl \
	$(vsldir)/builtin.vsl \
	$(vsldir)/tab.vsl \
	$(vsldir)/fonts.vsl \
	$(vsldir)/colors.vsl \
	$(vsldir)/list.vsl

ddd.vsl.h: $(vsldir)/ddd.vsl $(srcdir)/vsl2c.sed $(VSLSRC)
	$(CAT) $(vsldir)/ddd.vsl > tmp.c
	$(VSL_CPP) tmp.c | $(SED) -f $(srcdir)/vsl2c.sed | $(DELETE_CR) > $@
	$(RM) tmp.c

.PHONY: vsllib
vsllib: $(vsldir)/ddd.vsl $(VSLSRC)


# -----------------------------------------------------------------------------
# Lex & Yacc.
# -----------------------------------------------------------------------------

# YACC commands.
YY = yy

# LEX commands.
LEXTOCXX = $(srcdir)/lextoC

# The lex output root (lex.yy)
LEX_OUTPUT_ROOT = @LEX_OUTPUT_ROOT@

# VSL parsers.
vsl-lex.C: $(srcdir)/vsl-lex.L
	$(LEX) $(LFLAGS) $(srcdir)/vsl-lex.L

vsl-gramma.H vsl-gramma.C: $(srcdir)/vsl-gramma.Y
	$(YACC) $(YFLAGS) -d $(srcdir)/vsl-gramma.Y

VSLRead.$(OBJEXT): vsl-lex.C vsl-gramma.H vsl-gramma.C

# DDD regexp parsers.
rxscan.C: $(srcdir)/rxscan.L
	$(LEX) $(LFLAGS) $(srcdir)/rxscan.L

regexps.$(OBJEXT): rxscan.C



# -----------------------------------------------------------------------------
# Text files compiled into DDD.
# -----------------------------------------------------------------------------

# Script rules
.txt.C:
	@$(ECHO) "Creating $@"
	@( \
	$(ECHO) '// $@ -- generated automatically from `$<'"'."; \
	$(SED) '/^ *#/d' $< | \
	$(SED) 's/^ *include \([^"][^.]*\)\..*$$/#include "\1.C"/' | \
	$(SED) 's/^ *include "\([^"][^.]*\)[^"]*"/#include "\1.C"/' | \
	$(SED) '/^[^#]/s/\(["'"'"'\\]\)/\\\1/g' | \
	$(SED) '/^[^#]/s/.*/"&\\n"/' | \
	$(SED) 's//\\b/g' | \
	$(SED) 's/^$$/"\\n"/' \
	) > tmp.C; \
	$(CPP) -C -P -undef $(CPPFLAGS) $(DEFS) $(INCLUDE) tmp.C | \
	    $(DELETE_CR) > $@; \
	$(RM) tmp.C

# Reference.
# ddd.info.txt does NOT depend on ddd.info since we don't want it to get
# re-created after each configuration.
$(builddocdir)/ddd.info.txt: $(srcdir)/ddd.texi
	$(MAKE) ddd.info
	@-test -d $(builddocdir) || mkdir $(builddocdir)
	info --subnodes -o - -f $(srcdir)/ddd.info | $(DELETE_CR) > $@~ \
	    && $(MV) $@~ $@

$(builddocdir)/ddd.info.txt.gz: $(builddocdir)/ddd.info.txt
	$(COMPRESS) $? > $@~ && $(MV) $@~ $@

$(builddocdir)/ddd.info.txt.gz.C: $(builddocdir)/ddd.info.txt.gz $(STRINGIFY)
	-$(STRINGIFY) < $< > $@

show.$(OBJEXT): $(builddocdir)/ddd.info.txt.gz.C

# EPS code stuff.
$(srcdir)/header.str: $(srcdir)/header.ps
	$(SED) 's/^.*$$/"&\\n"/' $(srcdir)/header.ps | $(DELETE_CR) \
	    > $@~ && $(MV) $@~ $@

$(srcdir)/trailer.str: $(srcdir)/trailer.ps
	$(SED) 's/^.*$$/"&\\n"/' $(srcdir)/trailer.ps | $(DELETE_CR) \
	    > $@~ && $(MV) $@~ $@

$(srcdir)/eps-code.h: \
	$(srcdir)/header.str $(srcdir)/trailer.str $(srcdir)/eps-code.x
	$(SED) -e '/prolog/r $(srcdir)/header.str' \
	       -e '/trailer/r $(srcdir)/trailer.str' $(srcdir)/eps-code.x \
	    | $(DELETE_CR) > $@~ && $(MV) $@~ $@


# -----------------------------------------------------------------------------
# Demos.
# -----------------------------------------------------------------------------

# `make check' commands.

# A debugger for debugging DDD.  (gdb)
DEBUGGER = @DEBUGGER@

# The options for DDD when invoking `make check'.  ()
DDDFLAGS = @DEBUGGER_OPTION@

# The program to debug
DDDTARGET = cxxtest$(EXEEXT)

# For demonstration and debugging purposes
.PHONY: check
check: x11/Ddd ./$(ddd)$(EXEEXT) cxxtest$(EXEEXT) check-now

.PHONY: check-now
check-now:
	MALLOC_CHECK_=2 \
	DDD_HOME=$(srcdir)/.. \
	XUSERFILESEARCHPATH=%N XAPPLRESDIR=. \
	./$(ddd)$(EXEEXT) $(DDDFLAGS) $(DDDTARGET)

.PHONY: debug
debug: x11/Ddd ./$(ddd)$(EXEEXT) cxxtest$(EXEEXT) .gdbinit debug-now

.PHONY: debug-now
debug-now:
	MALLOC_CHECK_=2 \
	DDD_HOME=$(srcdir)/.. \
	XUSERFILESEARCHPATH=%N XAPPLRESDIR=. \
	$(DEBUGGER) ./$(ddd)$(EXEEXT)

# We don't want no optimizing, but debugging info in our test files
MAKE_DEBUG_FLAGS = \
	CXXFLAGS="`$(ECHO) '$(CXXFLAGS)' | \
	$(SED) 's/-O[^ ]*//' | $(SED) 's/-DNDEBUG//'`" \
	CFLAGS="`$(ECHO) '$(CFLAGS)' | \
	$(SED) 's/-O[^ ]*//' | $(SED) 's/-DNDEBUG//'`"

cxxtest.$(OBJEXT): $(srcdir)/cxxtest.C
	@case '$(CXXFLAGS)' in \
	*-O*) $(MAKE) $(MAKE_DEBUG_FLAGS) $@;; \
	*) set -x; \
	   $(CXXCOMPILE) -c @CXXDEBUG@ $(srcdir)/cxxtest.C -o $@;; \
	esac

ctest.$(OBJEXT): $(srcdir)/ctest.c
	@case '$(CFLAGS)' in \
	*-O*) $(MAKE) $(MAKE_DEBUG_FLAGS) $@;; \
	*) set -x; \
	   $(COMPILE) -c -g $(srcdir)/ctest.c -o $@;; \
	esac

sample.$(OBJEXT): $(srcdir)/sample.c
	@case '$(CFLAGS)' in \
	*-O*) $(MAKE) $(MAKE_DEBUG_FLAGS) $@;; \
	*) set -x; \
	   $(COMPILE) -c -g $(srcdir)/sample.c -o $@;; \
	esac

grabtest.$(OBJEXT): $(srcdir)/grabtest.C
	@case '$(CXXFLAGS)' in \
	*-O*) $(MAKE) $(MAKE_DEBUG_FLAGS) $@;; \
	*) set -x; \
	   $(CXXCOMPILE) -c @CXXDEBUG@ $(srcdir)/grabtest.C -o $@;; \
	esac

bug.$(OBJEXT):	$(srcdir)/bug.C
	@case '$(CXXFLAGS)' in \
	*-O*) $(MAKE) $(MAKE_DEBUG_FLAGS) $@;; \
	*) set -x; \
	   $(CXXCOMPILE) -c @CXXDEBUG@ $(srcdir)/bug.C -o $@;; \
	esac



# -----------------------------------------------------------------------------
# Icons.
# -----------------------------------------------------------------------------


# Icon rules
#.xpm.xbm:
$(toolbardir)/%.xbm:  $(srctoolbardir)/%.xpm
	@$(ECHO) "Creating $@ from $<"
	@mkdir -p $(toolbardir)
	@-base=`$(ECHO) $@ | $(SED) 's,.*/,,' | $(SED) 's/[.]x[bp]m.*//'`; \
	$(SED) 's/[	 ][cg]4*[ 	][#a-zA-Z0-9][#a-zA-Z0-9]*//g' $< | \
	$(SED) 's/[nN]one/white/g' | \
	$(XPMTOPPM) | $(PNMDEPTH) 255 | $(PPMTOPGM) | $(PGMTOPBM) | \
	$(PBMTOXBM) | $(SED) "s/noname/$${base}/g" | \
	$(SED) "s/static char/static unsigned char/g" > $@

#.xbm.xface:
#	@$(ECHO) "Creating $@"
#	@$(ECHO) "X-Face:`$(XBM2XFACE) $<`" | $(DELETE_CR) > $@~
#	@test -s $@~ && $(MV) $@~ $@ || ($(RM) $@~; test -s $@)


# This jewel makes an `emboss' effect in two steps:
# 1. Create a displaced mask in FILE-mask.pbm, using `pnmcut' and `pnmpaste'
# 2. Add the mask to FILE.xbm, using `pnmarith'.
#.xbm.xpmxx:
#	@$(ECHO) "Creating $@"
#	@-base=`$(ECHO) $@ | $(SED) 's,.*/,,' | $(SED) 's/[.]x[bp]m.*//'`; \
#	$(SED) 's/unsigned //' $< | \
#	$(XBMTOPBM) > $${base}-object.pbm; \
#	$(PNMMARGIN) 1 $${base}-object.pbm | \
#	$(PNMCUT) 0 0 29 25 | \
#	$(PNMINVERT) | \
#	$(PNMPASTE) -and $${base}-object.pbm 0 0 > $${base}-mask.pbm; \
#	$(PPMTOXPM) $${base}-object.pbm | \
#	$(SED) -e 's/#00*/grey50/' -e 's/#FF*/grey/' \
#	-e 's/\<black\>/grey50/' -e 's/\<white\>/grey/' | \
#	$(XPMTOPPM) > $${base}-button.ppm; \
#	$(PNMARITH) -add $${base}-button.ppm $${base}-mask.pbm | \
#	$(PPMTOXPM) | \
#	$(SED) 's/c #BE[BE]*/c none   g none   m none  s Background/' | \
#	$(SED) 's/c #7F[7F]*/c grey50 g grey50 m black/' | \
#	$(SED) 's/c #FF*/c white  g white  m white/' | \
#	$(SED) "s/noname/$${base}_xx_xpm/" | $(DELETE_CR) > $@~; \
#	$(RM) $${base}-object.pbm $${base}-mask.pbm $${base}-button.ppm
#	@test -s $@~ && $(MV) $@~ $@ || ($(RM) $@~; test -s $@)

#.xpm.xbmxx:
$(toolbardir)/%.xbmxx:  $(srctoolbardir)/%.xpm
	@$(ECHO) "Creating $@ from $<"
	@mkdir -p $(toolbardir)
	@-base=`$(ECHO) $@ | $(SED) 's,.*/,,' | $(SED) 's/[.]x[bp]m.*//'`; \
	$(SED) 's/[ 	]c[	 ][#a-zA-Z0-9][#a-zA-Z0-9]*//' $< | \
	$(SED) 's/ g black  / g grey50 /' | \
	$(SED) 's/ g white  / g grey75 /' | \
	$(SED) 's/g \([a-zA-Z0-9]*\) /c \1 g \1 /' | \
	$(SED) 's/[nN]one/white/g' | \
	$(XPMTOPPM) | $(PNMDEPTH) 255 | $(PPMTOPGM) | $(PGMTOPBM) | \
	$(PBMTOXBM) | $(SED) "s/noname/$${base}_xx/" | \
	$(SED) "s/static char/static unsigned char/g" > $@

# Icons and logos.

# The (derived) icons.
# Icon directories
icondir = $(top_srcdir)/icons
buildicondir = $(top_builddir)/icons
cursorsdir = $(icondir)/cursors
glyphsdir = $(icondir)/glyphs
tictactoedir = $(icondir)/tictactoe
toolbardir = $(buildicondir)/toolbar
srctoolbardir = $(icondir)/toolbar


.PHONY: icons
icons:	$(ICONS)
	@:

# All X bitmaps are derived from the XPM sources.

$(buildicondir)/dddmask.xpm: $(icondir)/ddd.xpm
	@test -d $(buildicondir) || mkdir $(buildicondir)
	$(SED) 's/[wW]hite/black/g' $(icondir)/ddd.xpm | $(DELETE_CR) > $@

$(buildicondir)/ddd.xbm: $(icondir)/ddd.xpm

#$(buildicondir)/ddd.xface: $(buildicondir)/ddd.xbm

$(buildicondir)/dddmask.xbm: $(icondir)/dddmask.xpm

# Original filter for dddsplash to extract g4 info
# $(SED) 's/[	 ][cmg][ 	][#a-zA-Z0-9][#a-zA-Z0-9]*//g' | \
#

$(buildicondir)/dddsplash.xbm: $(icondir)/dddsplash.xpm
	@test -d $(buildicondir) || mkdir $(buildicondir)
	@$(ECHO) "Creating $@"
	@-$(CAT) $(icondir)/dddsplash.xpm | \
	$(XPMTOPPM) | $(PNMDEPTH) 255 | $(PNMGAMMA) 0.4 | $(PPMTOPGM) | \
	$(PGMENHANCE) -7 | \
	$(PGMTOPBM) | $(PBMTOXBM) | $(SED) 's/noname/dddsplash/g' | \
	$(SED) "s/static char/static unsigned char/g" | $(DELETE_CR) > $@~
	@test -s $@~ && $(MV) $@~ $@ || ($(RM) $@~; test -s $@)

$(buildicondir)/dddlogo.xpm: $(icondir)/dddsplash.xpm
	@test -d $(buildicondir) || mkdir $(buildicondir)
	$(CONVERT) -fill white \
	-draw 'rectangle 0,138 409,139' -draw 'rectangle 408,0 409,139' $< $@


XBM_GLYPH_ICONS = \
	$(glyphsdir)/arrow.xbm \
	$(glyphsdir)/cond.xbm \
	$(glyphsdir)/dragarrow.xbm \
	$(glyphsdir)/dragcond.xbm \
	$(glyphsdir)/dragstop.xbm \
	$(glyphsdir)/dragtemp.xbm \
	$(glyphsdir)/greyarrow.xbm \
	$(glyphsdir)/greycond.xbm \
	$(glyphsdir)/greysignal.xbm \
	$(glyphsdir)/greystop.xbm \
	$(glyphsdir)/greytemp.xbm \
	$(glyphsdir)/pastarrow.xbm \
	$(glyphsdir)/signalarrow.xbm \
	$(glyphsdir)/stop.xbm \
	$(glyphsdir)/temp.xbm

XBM_CURSORS_ICONS = \
	$(cursorsdir)/time16.xbm \
	$(cursorsdir)/time16m.xbm \
	$(cursorsdir)/time32.xbm \
	$(cursorsdir)/time32m.xbm

XBM_TICTACTOE_ICONS = \
	$(tictactoedir)/circle.xbm \
	$(tictactoedir)/cross.xbm \
	$(tictactoedir)/empty.xbm

# XBM icons are derived from XPM sources
XPM_ICONS = \
	$(srctoolbardir)/breakat.xpm \
	$(srctoolbardir)/clearat.xpm \
	$(srctoolbardir)/cluster.xpm \
	$(srctoolbardir)/delete.xpm \
	$(srctoolbardir)/deref.xpm \
	$(srctoolbardir)/disable.xpm \
	$(srctoolbardir)/display.xpm \
	$(srctoolbardir)/findbwd.xpm \
	$(srctoolbardir)/findfwd.xpm \
	$(srctoolbardir)/enable.xpm \
	$(srctoolbardir)/hide.xpm \
	$(srctoolbardir)/lookup.xpm \
	$(srctoolbardir)/maketemp.xpm \
	$(srctoolbardir)/newbreak.xpm \
	$(srctoolbardir)/newdisplay.xpm \
	$(srctoolbardir)/newwatch.xpm \
	$(srctoolbardir)/plot.xpm \
	$(srctoolbardir)/print.xpm \
	$(srctoolbardir)/properties.xpm \
	$(srctoolbardir)/rotate.xpm \
	$(srctoolbardir)/set.xpm \
	$(srctoolbardir)/show.xpm \
	$(srctoolbardir)/uncluster.xpm \
	$(srctoolbardir)/undisplay.xpm \
	$(srctoolbardir)/unwatch.xpm \
	$(srctoolbardir)/watch.xpm 

# XBM icons are derived from XPM sources
XBM_ICONS = \
	$(toolbardir)/breakat.xbm \
	$(toolbardir)/clearat.xbm \
	$(toolbardir)/cluster.xbm \
	$(toolbardir)/delete.xbm \
	$(toolbardir)/deref.xbm \
	$(toolbardir)/disable.xbm \
	$(toolbardir)/display.xbm \
	$(toolbardir)/findbwd.xbm \
	$(toolbardir)/findfwd.xbm \
	$(toolbardir)/enable.xbm \
	$(toolbardir)/hide.xbm \
	$(toolbardir)/lookup.xbm \
	$(toolbardir)/maketemp.xbm \
	$(toolbardir)/newbreak.xbm \
	$(toolbardir)/newdisplay.xbm \
	$(toolbardir)/newwatch.xbm \
	$(toolbardir)/plot.xbm \
	$(toolbardir)/print.xbm \
	$(toolbardir)/properties.xbm \
	$(toolbardir)/rotate.xbm \
	$(toolbardir)/set.xbm \
	$(toolbardir)/show.xbm \
	$(toolbardir)/uncluster.xbm \
	$(toolbardir)/undisplay.xbm \
	$(toolbardir)/unwatch.xbm \
	$(toolbardir)/watch.xbm 

# XPMXX icons (insensitive XPM icons) are derived from XBM sources
XPM_XX_ICONS = \
	$(toolbardir)/breakat.xpmxx \
	$(toolbardir)/clearat.xpmxx \
	$(toolbardir)/cluster.xpmxx \
	$(toolbardir)/delete.xpmxx \
	$(toolbardir)/deref.xpmxx \
	$(toolbardir)/disable.xpmxx \
	$(toolbardir)/display.xpmxx \
	$(toolbardir)/findbwd.xpmxx \
	$(toolbardir)/findfwd.xpmxx \
	$(toolbardir)/enable.xpmxx \
	$(toolbardir)/hide.xpmxx \
	$(toolbardir)/lookup.xpmxx \
	$(toolbardir)/maketemp.xpmxx \
	$(toolbardir)/newbreak.xpmxx \
	$(toolbardir)/newdisplay.xpmxx \
	$(toolbardir)/newwatch.xpmxx \
	$(toolbardir)/plot.xpmxx \
	$(toolbardir)/print.xpmxx \
	$(toolbardir)/properties.xpmxx \
	$(toolbardir)/rotate.xpmxx \
	$(toolbardir)/set.xpmxx \
	$(toolbardir)/show.xpmxx \
	$(toolbardir)/uncluster.xpmxx \
	$(toolbardir)/undisplay.xpmxx \
	$(toolbardir)/unwatch.xpmxx \
	$(toolbardir)/watch.xpmxx 


# XBMXX icons (insensitive XBM icons) are derived from XPM sources
XBM_XX_ICONS = \
	$(toolbardir)/breakat.xbmxx \
	$(toolbardir)/clearat.xbmxx \
	$(toolbardir)/cluster.xbmxx \
	$(toolbardir)/delete.xbmxx \
	$(toolbardir)/deref.xbmxx \
	$(toolbardir)/disable.xbmxx \
	$(toolbardir)/display.xbmxx \
	$(toolbardir)/findbwd.xbmxx \
	$(toolbardir)/findfwd.xbmxx \
	$(toolbardir)/enable.xbmxx \
	$(toolbardir)/hide.xbmxx \
	$(toolbardir)/lookup.xbmxx \
	$(toolbardir)/maketemp.xbmxx \
	$(toolbardir)/newbreak.xbmxx \
	$(toolbardir)/newdisplay.xbmxx \
	$(toolbardir)/newwatch.xbmxx \
	$(toolbardir)/plot.xbmxx \
	$(toolbardir)/print.xbmxx \
	$(toolbardir)/properties.xbmxx \
	$(toolbardir)/rotate.xbmxx \
	$(toolbardir)/set.xbmxx \
	$(toolbardir)/show.xbmxx \
	$(toolbardir)/uncluster.xbmxx \
	$(toolbardir)/undisplay.xbmxx \
	$(toolbardir)/unwatch.xbmxx \
	$(toolbardir)/watch.xbmxx

# All icons
# Order is significant here!  First sources, then derived files.
ICONS = \
	$(icondir)/ddd.xpm \
	$(icondir)/ddd.xbm \
	$(icondir)/dddback.xpm \
	$(icondir)/dddmask.xpm \
	$(icondir)/dddmask.xbm \
	$(icondir)/dddsplash.xpm \
	$(buildicondir)/dddsplash.xbm \
	$(XPM_ICONS) \
	$(XBM_CURSORS_ICONS) \
	$(XBM_GLYPH_ICONS) \
	$(XBM_TICTACTOE_ICONS) \
	$(XBM_ICONS) \
	$(XPM_XX_ICONS) \
	$(XBM_XX_ICONS)

# -----------------------------------------------------------------------------
# DDD Manual.
# -----------------------------------------------------------------------------

info_TEXINFOS = ddd.texi ddd-themes.texi
ddd_TEXINFOS = \
	$(srcdir)/config.texi \
	$(srcdir)/macros.texi \
	$(srcdir)/gpl.texinfo \
	$(srcdir)/gfdl.texinfo
ddd_themes_TEXINFOS = \
	$(srcdir)/config.texi \
	$(srcdir)/macros.texi \
	$(srcdir)/gpl.texinfo \
	$(srcdir)/gfdl.texinfo
texidir = $(srcdir)/../texinfo
TEXINFO_TEX = $(texidir)

$(srcdir)/config.texi: cfg.texi
	@$(CMP) cfg.texi $@ 2> /dev/null || \
	( $(CAT) cfg.texi > $@~ && $(MV) $@~ $@ )

$(srcdir)/gpl.texinfo: $(texidir)/gpl.texinfo
	$(RM) $@; cp $(texidir)/gpl.texinfo $@

$(srcdir)/gfdl.texinfo: $(texidir)/gfdl.texinfo
	$(RM) $@; cp $(texidir)/gfdl.texinfo $@

builddocdir = $(top_builddir)/doc

# The DDD manual in PDF format, including all pictures.

.PHONY: pdf
pdf: $(builddocdir)/ddd.pdf $(builddocdir)/ddd-themes.pdf

$(builddocdir)/ddd.pdf: ddd.pdf
	@-test -d $(builddocdir) || mkdir $(builddocdir)
	$(INSTALL_DATA) ddd.pdf $@

$(builddocdir)/ddd-themes.pdf: ddd-themes.pdf
	@-test -d $(builddocdir) || mkdir $(builddocdir)
	$(INSTALL_DATA) ddd-themes.pdf $@

ddd.pdf: $(PDF_IMAGES) $(ddd_TEXINFOS)

ddd-themes.pdf: $(ddd_themes_TEXINFOS)



# The DDD manual in HTML format.

htmldir = $(builddocdir)/html

.PHONY: html
html: $(htmldir)/ddd.html $(htmldir)/ddd-themes.html

$(htmldir)/ddd.html $(htmldir)/ddd-themes.html: $(JPG_IMAGES) \
	$(srcdir)/ddd.texi $(srcdir)/ddd-themes.texi \
	style.css $(srcdir)/fix-html.sed
	@-test -d $(htmldir) || mkdir -p $(htmldir)
	@-test -d $(htmldir)/PICS || mkdir -p $(htmldir)/PICS
	@-test -d PICS || mkdir -p PICS
	$(RM) ddd*.html
	$(MAKEINFOHTML) -I $(srcdir) -I $(texidir) $(srcdir)/ddd-themes.texi --no-split
	$(MAKEINFOHTML) -I $(srcdir) -I $(texidir) $(srcdir)/ddd.texi --no-split
	for file in ddd*.html; do \
		$(SED) -f $(srcdir)/fix-html.sed $$file | \
		$(SED) 's/$(IMGEXT)/\$(IMGEXT2)/g' > $$file~ && \
		$(MV) $$file~ $$file; \
	done
	cd $(htmldir) && $(RM) ddd*.html style.css PICS/*
	$(INSTALL_DATA) ddd*.html $(srcdir)/style.css $(htmldir)
	($(ECHO) 'index.html:'; $(ECHO) '	$(LN_S) ddd.html index.html') \
	 > $(htmldir)/Makefile
	@$(ECHO) Installing images...
	@$(INSTALL_DATA) $(JPG_IMAGES) $(htmldir)/PICS
	@$(ECHO) Installing images...done.

# Manual page
man_MANS = ddd.1

# `ddd.man' has 8-bit format, `ddd.1' has 7-bit format
ddd.1:   ddd.man $(srcdir)/unumlaut.sed
	$(MV) $< $@



# -----------------------------------------------------------------------------
# DDD Manual Pictures.
# -----------------------------------------------------------------------------

# The image extension (.jpg, .png, or .gif)
IMGEXT     = .png
IMGEXT2    = .jpg

# Width of image in HTML manual (pixels)
IMAGE_WIDTH = 800

# Some XPM/PPM/PostScript converters, from the netpbm and pbmplus packages.
PBMTOXBM   = pbmtoxbm
PGMENHANCE = pgmenhance
PGMTOPBM   = pgmtopbm -threshold
PNMARITH   = pnmarith
PNMCUT     = pnmcut
PNMDEPTH   = pnmdepth
PNMGAMMA   = pnmgamma
PNMINVERT  = pnminvert
PNMMARGIN  = pnmmargin
PNMPASTE   = pnmpaste
PNMTOPS    = pnmtops
PPMTOPGM   = ppmtopgm
PPMTOXPM   = ppmtoxpm
XBMTOPBM   = xbmtopbm
XPMTOPPM   = xpmtoppm

# The ImageMagick `convert' program (convert)
CONVERT    = convert

# The fig2dev command.  (fig2dev)
FIG2DEV = fig2dev
FIG2PDF = $(FIG2DEV) -L pdf
FIG2JPG = $(FIG2DEV) -L jpeg

# The Ghostscript command.  (gs)
GS = gs
GSOPT = -q -sDEVICE=pdfwrite -dCompatibilityLevel=1.4

# We use giftoppm/ppmtogif to get optimal GIF compression.
.fig.pdf:
	@-test -d $(buildpicdir) || mkdir $(buildpicdir)
	(cd `dirname $<` && $(FIG2PDF) `basename $<` ) > $@-17
	$(GS) $(GSOPT) -o $@ $@-17
	rm $@-17

%.jpg: %.fig 
	@-test -d $(buildpicdir) || mkdir $(buildpicdir)
	$(FIG2JPG) $< $@

# Our `texinfo.tex' must reside in the current directory, otherwise
# texi2dvi will use the default.
.texi.pdf:
	@-test -d $(buildpicdir) || mkdir $(buildpicdir)
	@-test -f texinfo.tex || $(LN_S) $(texidir)/texinfo.tex .
	$(TEXI2PDF) -I $(srcdir) -I $(texidir) $<

# PostScript pictures in the DDD manual.
# All of these are generated from FIG and XPM files.
picdir = $(srcdir)/PICS
buildpicdir = $(top_builddir)/ddd/PICS

DOC_IMAGES = \
	ddd-aliases		\
	ddd-all			\
	ddd-arguments		\
	ddd-attach		\
	ddd-backtrace		\
	ddd-bp-popup		\
	ddd-bp-properties	\
	ddd-button-editor	\
	ddd-clusters		\
	ddd-code		\
	ddd-data-prefs		\
	ddd-define-command	\
	ddd-display		\
	ddd-drag		\
	ddd-edit-breakpoints	\
	ddd-edit-displays	\
	ddd-examine		\
	ddd-font-prefs		\
	ddd-general-prefs	\
	ddd-helpers		\
	ddd-hide-display	\
	ddd-history		\
	ddd-layout		\
	ddd-line-popup		\
	ddd-locals		\
	ddd-open		\
	ddd-open-session	\
	ddd-plots		\
	ddd-print-graph		\
	ddd-print-output	\
	ddd-print-popup		\
	ddd-registers		\
	ddd-repeats		\
	ddd-rotate-display	\
	ddd-save-session	\
	ddd-select-display	\
	ddd-separate		\
	ddd-set			\
	ddd-settings		\
	ddd-shortcut-editor	\
	ddd-shortcuts		\
	ddd-signals		\
	ddd-source		\
	ddd-source-popup	\
	ddd-source-prefs	\
	ddd-startup-prefs	\
	ddd-status-displays	\
	ddd-suppress		\
	ddd-themes		\
	ddd-threads		\
	ddd-tool		\
	ddd-toolbar		\
	ddd-toolbars		\
	ddd-value-tip		\
	tut-backtrace		\
	tut-display		\
	tut-finish		\
	tut-invoke		\
	tut-run			\
	tut-set			\
	tut-value

PDF_IMAGES = $(addprefix $(buildpicdir)/,$(addsuffix .pdf,$(DOC_IMAGES)))

FIG_IMAGES = $(addprefix $(picdir)/,$(addsuffix .fig,$(DOC_IMAGES)))

JPG_IMAGES := $(addprefix $(buildpicdir)/,$(addsuffix .jpg,$(DOC_IMAGES)))

PNG_IMAGES := $(addprefix $(picdir)/,$(addsuffix .png,$(DOC_IMAGES))) \
	$(picdir)/ddd-drag1.png			\
	$(picdir)/ddd-drag2.png			\
	$(picdir)/ddd-drag3.png			\
	$(picdir)/ddd-toolbar-1.png		\
	$(picdir)/ddd-toolbar-2.png		\
	$(picdir)/ddd-toolbar-3.png		\
	$(picdir)/ddd-toolbar-4.png

# All derived pictures
IMAGES = $(PDF_IMAGES)

# Included pictures

$(buildpicdir)/dddsplash.gif: $(icondir)/dddsplash.xpm
	$(CONVERT) $(icondir)/dddsplash.xpm $@

$(buildpicdir)/dddsplash.jpg: $(icondir)/dddsplash.xpm
	$(CONVERT) -quality 100 $(icondir)/dddsplash.xpm $@

$(buildpicdir)/dddsplash.png: $(icondir)/dddsplash.xpm
	$(CONVERT) -quality 100 $(icondir)/dddsplash.xpm $@

$(buildpicdir)/dddlogo.gif: $(buildicondir)/dddlogo.xpm
	$(CONVERT) $(buildicondir)/dddlogo.xpm $@

$(buildpicdir)/dddlogo.png: $(icondir)/dddlogo.xpm
	$(CONVERT) -quality 100 $(icondir)/dddlogo.xpm $@

$(buildpicdir)/dddback.gif: $(icondir)/dddback.xpm
	$(CONVERT) $(icondir)/dddback.xpm $@

$(buildpicdir)/dddback.jpg: $(icondir)/dddback.xpm
	$(CONVERT) -quality 100 $(icondir)/dddback.xpm $@

$(buildpicdir)/dddback.png: $(icondir)/dddback.xpm
	$(CONVERT) -quality 100 $(icondir)/dddback.xpm $@

# -----------------------------------------------------------------------------
# Configuration.
# -----------------------------------------------------------------------------

# Architecture (usually overridden by the top-level Makefile).

# The host we were compiled on.  (CPU-COMPANY-SYSTEM)
host_canonical = @host@

# The target we were compiled for.  (CPU-COMPANY-SYSTEM)
target_canonical = @host@


# Special rules for configuration.
# autoheader might not change config.h.in
stamp-h: config.h.in $(top_builddir)/config.status
	CONFIG_FILES= CONFIG_HEADERS=config.h $(top_builddir)/config.status
	$(DATE) | $(DELETE_CR) > $@~ && $(MV) $@~ $@

$(srcdir)/config.h.in:
	cd $(srcdir)/.. && $(AUTOHEADER)

# Special program includes
# Note: we use `build.h' instead of `./build.h', because `./build.h'
# breaks SGI make.
version.h: vr.h
	$(CMP) vr.h $@ 2> /dev/null || \
	    ( $(CAT) vr.h | $(DELETE_CR) > $@~ && $(MV) $@~ $@ )
build.h: bld.h
	$(CMP) bld.h $@ 2> /dev/null || \
	    ( $(CAT) bld.h | $(DELETE_CR) > $@~ && $(MV) $@~ $@ )
host.h: $(srcdir)/host.h.in $(top_builddir)/config.status
	$(CAT) $(srcdir)/host.h.in | \
	$(SED) "s%@HOST_CANONICAL@%$(host_canonical)%" | \
	$(SED) "s%@TARGET_CANONICAL@%$(target_canonical)%" | \
	    $(DELETE_CR) > $@~ && $(MV) $@~ $@
root.h: $(srcdir)/root.h.in $(top_builddir)/config.status
	$(CAT) $(srcdir)/root.h.in | \
	$(SED) "s%@ROOT@%$(dddrootdir)%" | \
	$(SED) "s%@ALT_ROOT@%$(pkgdatadir)%" | \
	    $(DELETE_CR) > $@~ && $(MV) $@~ $@


# -----------------------------------------------------------------------------
# Installation.
# -----------------------------------------------------------------------------

dddapp_DATA = x11/Ddd

# -----------------------------------------------------------------------------
# Distribution.
# -----------------------------------------------------------------------------

# Architecture-independent files required for building DDD.
# In a distribution, these should be already built.
#
# Order is significant here!  First source files, then derived files.
PROG_STUFF = vsl-lex.L vsl-lex.C \
	     vsl-gramma.Y vsl-gramma.H vsl-gramma.C \
	     rxscan.L rxscan.C \
             $(srcdir)/../doc/TIPS $(srcdir)/../m4/tips.m4 \
	     $(srcdir)/tips2m4.awk $(top_builddir)/ddd/tips.html \
	     $(srcdir)/../m4/macros.m4 $(srcdir)/../m4/colors.m4 \
             $(srcdir)/../m4/Ddd.in.m4 $(srcdir)/x11/Ddd.in \
	     host.h.in $(srcdir)/vsl2c.sed \
             $(srcdir)/../m4/ddd.vsl.m4 $(vsldir)/ddd.vsl \
             root.h.in \
	     $(srcdir)/ddd.info \
             xlibdir.txt xlibdir.C $(srcdir)/header.str \
	     $(srcdir)/trailer.str $(srcdir)/eps-code.x eps-code.h \
	     .gdbinit $(ICONS)

# Additional files to be included in the distribution.
DIST_STUFF = $(srcdir)/header.ps $(srcdir)/trailer.ps \
	     $(builddocdir)/ddd.pdf \
	     $(builddocdir)/ddd-themes.pdf \
	     $(htmldir)/ddd.html $(srcdir)/ad2c.sed \
	     style.css $(srcdir)/fix-html.sed \
	     $(srcdir)/unumlaut.sed ddd.desktop \
	     $(srcdir)/../doc/ANNOUNCE $(srcdir)/../doc/AUTHORS  \
	     $(srcdir)/../doc/COPYING  $(srcdir)/../doc/COPYING.DOC  \
	     $(srcdir)/../doc/COPYING.LESSER  $(srcdir)/../doc/CREDITS  \
	     $(srcdir)/../doc/FONTS  $(srcdir)/../doc/INSTALL  \
	     $(srcdir)/../doc/NEWS  $(srcdir)/../doc/NEWS-OLD  \
	     $(srcdir)/../doc/NICKNAMES  $(srcdir)/../doc/README  \
	     $(srcdir)/../doc/TIPS  $(srcdir)/../doc/ddd-paper.pdf  \
	     $(srcdir)/../doc/ddd-paper.ps  $(srcdir)/../doc/sample.dddinit

# Let automake know what we need.
EXTRA_DIST = $(PROG_STUFF) $(DIST_STUFF) $(IMAGES)

# Make sure all this is built before DDD.
ddd.$(OBJEXT): $(PROG_STUFF)

# These should not go into the distribution.
DISTCLEANFILES = build.h host.h root.h ../config.cache \
	$(top_builddir)/ddd/stamp-h $(man_MANS) \
	version.h Ddd.ad.h

# `make clean' should also remove these temporary Texinfo files.
CLEANFILES = ddd.au ddd.cm ddd.cms ddd.en ddd.fl ddd.fls ddd.lb ddd.lbs \
	ddd.tmp ddd.html ../doc/html/ddd.html ddd.pdf ../doc/ddd.pdf \
	ddd-themes.au ddd-themes.fl ddd-themes.fls \
	ddd-themes.tmp ddd-themes.html ../doc/html/ddd-themes.html \
	ddd-themes.pdf ../doc/ddd-themes.pdf

# Have `make maintainer-clean' remove _all_ derived files.
MAINTAINERCLEANFILES = Ddd.in ddd.vsl.h ddd.info.txt.gz gfdl.texinfo \
	ddd.info.txt.gz.C ddd.info \
	ddd.info.txt tips.m4 gpl.texinfo vsl-lex.C \
	config.h.in config.texi vsl-gramma.C \
	vsl-gramma.H xlibdir.C trailer.str tips.html \
	header.str version.h rxscan.C \
	ddd/PICS/*.gif \
	ddd/PICS/*.jpg \
	ddd/PICS/*.pdf \
	$(buildicondir)/ddd.xface $(buildicondir)/dddsplash.xbm \
	$(vsldir)/ddd.vsl

# `make diststuff' creates all files required for a distribution.
diststuff: $(EXTRA_DIST)

# `make progstuff' creates all files required for building DDD.
progstuff: $(PROG_STUFF)


desktop_DATA = ddd.desktop

ddddoc_DATA = $(srcdir)/../doc/NEWS $(srcdir)/../doc/COPYING \
	      $(srcdir)/../doc/CREDITS


