// $Id$ 
// StringBox class

// Copyright (C) 1995 Technische Universitaet Braunschweig, Germany.
// Written by Andreas Zeller <zeller@gnu.org>.
// 
// This file is part of DDD.
// 
// DDD is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public
// License as published by the Free Software Foundation; either
// version 3 of the License, or (at your option) any later version.
// 
// DDD is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
// See the GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public
// License along with DDD -- see the file COPYING.
// If not, see <http://www.gnu.org/licenses/>.
// 
// DDD is the data display debugger.
// For details, see the DDD World-Wide-Web page, 
// `http://www.gnu.org/software/ddd/',
// or send a mail to the DDD developers <ddd@gnu.org>.

char StringBox_rcsid[] = 
    "$Id$";

#include "StringBox.h"
#include "printBox.h"

#include "base/strclass.h"
#include "base/assert.h"
#include "base/cook.h"

#include <X11/Xlib.h>
#include <X11/Intrinsic.h>
#include <ctype.h>
#include <sstream>

#include "vslsrc/VSEFlags.h"

// set this to 1 if you want to have the box a font-specific height
#define USE_MAX_BOUNDS 1


DEFINE_TYPE_INFO_1(StringBox, PrimitiveBox)

// StringBox

FontTable *StringBox::fontTable = 0;
bool StringBox::quoted = false;

// Recompute size
Box *StringBox::resize()
{
    if (_font != 0)
    {
#if !HAVE_FREETYPE
	int direction, font_ascent, font_descent;
	XCharStruct overall;

	XTextExtents(_font, _string.chars(), _string.length(),
	    &direction, &font_ascent, &font_descent, &overall);

#if USE_MAX_BOUNDS
	XCharStruct max_bounds = _font->max_bounds;

	_ascent = max_bounds.ascent;
	thesize() = BoxSize(overall.width,
			    max_bounds.ascent + max_bounds.descent);
#else
	_ascent = font_ascent;
	thesize() = BoxSize(extents.width, extents.height);
#endif
#else
        XGlyphInfo extents;
	XftTextExtents8(fontTable->getDisplay(), _font, (const FcChar8*)_string.chars(), _string.length(), &extents);
        _ascent = _font->ascent;
        thesize() = BoxSize(extents.width, _font->height);
#endif
    }

    return this;
}

// Draw
void StringBox::_draw(Widget w, 
		      const BoxRegion& r, 
		      const BoxRegion&, 
		      GC gc,
		      bool) const
{
    BoxPoint origin = r.origin();
#if !HAVE_FREETYPE
    if (_font != 0)
	XSetFont(XtDisplay(w), gc, _font->fid);

    XDrawString(XtDisplay(w), XtWindow(w), gc, origin[X], origin[Y] + _ascent,
		_string.chars(), _string.length());
#else
    Visual *visual = DefaultVisual(XtDisplay(w), DefaultScreen(XtDisplay(w)));
    Colormap cmap = DefaultColormap(XtDisplay(w),  DefaultScreen(XtDisplay(w)));
    XftDraw *draw = XftDrawCreate(XtDisplay(w), XtWindow(w), visual, cmap);

    XGCValues gc_values;
    XGetGCValues(XtDisplay(w), gc, GCForeground, &gc_values);

    XftColor color;
    XColor xcol;
    xcol.pixel = gc_values.foreground;
    XQueryColor(XtDisplay(w), DefaultColormap(XtDisplay(w), DefaultScreen(XtDisplay(w))), &xcol);
    color.color.red = xcol.red;
    color.color.blue = xcol.blue;
    color.color.green = xcol.green;
    color.color.alpha = 0xFFFF;

    XftDrawStringUtf8(draw, &color, _font, origin[X], origin[Y] + _ascent, (const FcChar8*)_string.chars(), _string.length());
    XftColorFree(XtDisplay(w), visual, cmap, &color);
    XftDrawDestroy(draw);
#endif
}


void StringBox::dump(std::ostream& s) const
{
    const char *quote = "\"";
    if (StringBox::quoted)
	quote = "\\\"";

    s << quote;
    for (unsigned i = 0; i < _string.length(); i++)
    {
	if (_string[i] == '\"')
	    s << quote;
	else
	    s << _string[i];
    }
    s << quote;

    if (VSEFlags::include_font_info)
	s << " (font: \"" << _fontname << "\")";
}

void StringBox::newFont(const string& fontname)
{
    _fontname = fontname;
    newFont();
}

void StringBox::newFont()
{
    if (fontTable != 0)
	_newFont((*fontTable)[_fontname]);
}

// Print
typedef struct fontmap {
	const char *xfont ;
	const char *psfont ;
	int figfont ;
} FONTMAP ;

// mapping between X11 fonts, PostScript fonts and xfig font numbers
static FONTMAP const map[] = {
{"fixed",                                "/Courier",                     12},
{"-*-times-medium-r-*-",                 "/Times-Roman",                  0},
{"-*-times-medium-*-*-",                 "/Times-Italic",                 1},
{"-*-times-bold-r-*-",                   "/Times-Bold",                   2},
{"-*-times-bold-*-*-",                   "/Times-BoldItalic",             3},
{"-*-courier-medium-r-*-",               "/Courier",                     12},
{"-*-courier-medium-*-*-",               "/Courier-Oblique",             13},
{"-*-courier-bold-r-*-",                 "/Courier-Bold",                14},
{"-*-courier-bold-*-*-",                 "/Courier-BoldOblique",         15},
{"-*-helvetica-medium-r-*-",             "/Helvetica-Narrow",            16},
{"-*-helvetica-medium-*-*-",             "/Helvetica-NarrowOblique",     17},
{"-*-helvetica-bold-r-*-",               "/Helvetica",                   18},
{"-*-helvetica-bold-*-*-",               "/Helvetica-Oblique",           19},
{"-*-lucidatypewriter-medium-r-*-",      "/Courier",                     12},
{"-*-lucidatypewriter-medium-*-*-",      "/Courier-Oblique",             13},
{"-*-lucidatypewriter-bold-r-*-",        "/Courier-Bold",                14},
{"-*-lucidatypewriter-bold-*-*-",        "/Courier-BoldOblique",         15},
{"-*-new century schoolbook-bold-*-",    "/NewCenturySchlbk-BoldItalic", 27},
{"-*-new century schoolbook-bold-r-*",   "/NewCenturySchlbk-Bold",       26},
{"-*-new century schoolbook-medium-*-*", "/NewCenturySchlbk-Italic",     25},
{"-*-new century schoolbook-medium-r-*", "/NewCenturySchlbk-Roman",      24},
{"-*-symbol-medium-",                    "/Symbol",                      32},
{"-*-liberation serif-medium-r-*-",	 "/Times-Roman",                  0},
{"-*-liberation serif-medium-*-*-",      "/Times-Italic",                 1},
{"-*-liberation serif-bold-r-*-",	 "/Times-Bold",                   2},
{"-*-liberation serif-bold-*-*-",	 "/Times-BoldItalic",             3},
{"-*-liberation mono-medium-r-*-",	 "/Courier",                     12},
{"-*-liberation mono-medium-*-*-",	 "/Courier-Oblique",             13},
{"-*-liberation mono-bold-r-*-",	 "/Courier-Bold",                14},
{"-*-liberation mono-bold-*-*-",	 "/Courier-BoldOblique",         15},
{"-*-liberation sans-medium-r-*-",	 "/Helvetica-Narrow",            16},
{"-*-liberation sans-medium-*-*-",	 "/Helvetica-NarrowOblique",     17},
{"-*-liberation sans-bold-r-*-",	 "/Helvetica",                   18},
{"-*-liberation sans-bold-*-*-",	 "/Helvetica-Oblique",           19},
};

static int mappings = sizeof (map) / sizeof (FONTMAP) ;

/*
 * matchFont
 */

static const FONTMAP *matchFont(const char *xfont) 
{
    const FONTMAP *fmap = &map[0] ;
    int match = 1;
    int i = 0;
    
    while (i < mappings && match != 0) {
	match = strncmp (map[i].xfont, xfont, strlen(map[i].xfont)) ;
	i++ ;
    } 
    if (match == 0) {
	fmap = &map[--i] ;
    }
    return fmap;
}


void StringBox::_print(std::ostream& os, 
		       const BoxRegion& region, 
		       const PrintGC& gc) const
{
    // Don't draw empty strings
    if (str().empty())
	return;

    BoxPoint origin = region.origin() ;
    const FONTMAP *fmap = matchFont (fontName_c());

    if (gc.isFig()) {
	os << TEXTHEAD1 << fmap->figfont << " "
	   << size(Y) - 3 << " " << TEXTHEAD2
	   << size(X) << " " << size(Y) << " "
	   << origin[X] << " " << origin [Y] + size(Y) - 2 << " "
	   << str() << "\001\n";
    } else if (gc.isPostScript()) {
	os << fmap->psfont << " " << size(X) << " " << size(Y)
	   << " " << origin[X] << " " << origin[Y] + size(Y) << " "
	   << "(" << pscook(str()) << ") text*\n";
    }
}   
