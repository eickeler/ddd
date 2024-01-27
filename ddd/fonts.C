// $Id$ -*- C++ -*-
// Setup DDD fonts

// Copyright (C) 1998 Technische Universitaet Braunschweig, Germany.
// Copyright (C) 2003 Free Software Foundation, Inc.
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

char fonts_rcsid[] = 
    "$Id$";

#include "config.h"
#include "fonts.h"
#include "x11/charsets.h"

#include "AppData.h"
#include "x11/DestroyCB.h"
#include "agent/LiterateA.h"
#include "template/StringSA.h"
#include "motif/TextSetS.h"
#include "assert.h"
#include "x11/converters.h"
#include "base/cook.h"
#include "ddd.h"
#include "x11/events.h"
#include "shell.h"
#include "status.h"
#include "base/strclass.h"
#include "string-fun.h"
#include "post.h"
#include "agent/TimeOut.h"

#include <stdlib.h>		// atoi()
#include <ctype.h>
#include <Xm/TextF.h>
#include <Xm/Text.h>
#include <Xm/PushB.h>
#include <X11/Xatom.h>		// XA_...

#include <fontconfig/fontconfig.h>

#include <algorithm>

//-----------------------------------------------------------------------------
// Return X font attributes
//-----------------------------------------------------------------------------

//  1     2    3    4     5     6  7     8    9    10   11  12   13     14
// -fndry-fmly-wght-slant-sWdth-ad-pxlsz-ptSz-resx-resy-spc-avgW-rgstry-encdng

const int Foundry       = 1;
const int Family        = 2;
const int Weight        = 3;
const int Slant         = 4;
// const int sWidth     = 5;
// const int Ad         = 6;
// const int PixelSize  = 7;
const int PointSize     = 8;
// const int ResX       = 9;
// const int ResY       = 10;
// const int Spacing    = 11;
// const int AvgWidth   = 12;
// const int Registry   = 13;
// const int Encoding   = 14;

const int AllComponents = 14;

typedef int FontComponent;

// Return the Nth component from NAME, or DEFAULT_VALUE if none
static string component(string name, FontComponent n)
{
    // If name does not begin with `-', assume it's a font family
    if (!name.contains('-', 0))
	name.prepend("-*-");

    // Let I point to the Nth occurrence of `-'
    int i = -1;
    while (n >= Foundry && (i = name.index('-', i + 1)) >= 0)
	n--;

    string w;
    if (i >= 0)
    {
	w = name.after(i);
	if (w.contains('-'))
	    w = w.before('-');
    }

    return w;
}


//-----------------------------------------------------------------------------
// Access X font resources
//-----------------------------------------------------------------------------

// User-specified values
static string userfont(const AppData& ad, DDDFont font)
{
    switch (font) 
    {
    case DefaultDDDFont:
	return ad.default_font;
    case VariableWidthDDDFont:
	return ad.variable_width_font;
    case FixedWidthDDDFont:
	return ad.fixed_width_font;
    case DataDDDFont:
	return ad.data_font;
    }

    assert(0);
    ::abort();
    return "";			// Never reached
}

// Return a symbolic name for FONT
static string font_type(DDDFont font)
{
    switch (font)
    {
    case DefaultDDDFont:
	return "default font";
    case VariableWidthDDDFont:
 	return "variable width font";
    case FixedWidthDDDFont:
 	return "fixed width font";
    case DataDDDFont:
 	return "data font";
    }

    assert(0);
    ::abort();
    return "";			// Never reached
}

// defaults to use if nothing is specified
static string fallbackfont(DDDFont font)
{
    switch (font) 
    {
    case DefaultDDDFont:
	return "-misc-liberation sans-bold-r-normal--0-0-0-0-p-0-iso8859-1";
    case VariableWidthDDDFont:
	return "-misc-liberation sans-medium-r-normal--0-0-0-0-p-0-iso8859-1";
    case FixedWidthDDDFont:
    case DataDDDFont:
	return "-misc-liberation mono-bold-r-normal--0-0-0-0-m-0-iso8859-1";
    }

    assert(0);
    ::abort();
    return "";			// Never reached
}

// Fetch a component
static string component(const AppData& ad, DDDFont font, FontComponent n)
{
    if (n == PointSize)
    {
	int sz = 0;
	switch(font)
	{
	case DefaultDDDFont:
	    sz = ad.default_font_size;
	    break;

	case VariableWidthDDDFont:
	    sz = ad.variable_width_font_size;
	    break;

	case FixedWidthDDDFont:
	    sz = ad.fixed_width_font_size;
	    break;

	case DataDDDFont:
	    sz = ad.data_font_size;
	    break;
	}

	if (sz<80)
            sz = 100;

	return itostring(sz);
    }

    string w = component(userfont(ad, font), n);
    if (w.empty())		// nothing specified
	w = component(fallbackfont(font), n);
    return w;
}



//-----------------------------------------------------------------------------
// Create an X font name
//-----------------------------------------------------------------------------

static string override(FontComponent new_n, 
		       const string& new_value, const string& font = "")
{
    string new_font;
    for (FontComponent n = Foundry; n <= AllComponents; n++)
    {
	new_font += '-';
	new_font +=
	  (n == new_n) ?
	  new_value :
	  component(font, n);
    }

    return new_font;
}

string make_font(const AppData& ad, DDDFont base, const string& override)
{
    string font;
    for (FontComponent n = Foundry; n <= AllComponents; n++)
    {
	font += '-';
	string w = component(override, n);
	if (w.empty() || w == " ")
	    w = component(ad, base, n);
	font += w;
    }

#if 0
    std::clog << "make_font(" << font_type(base) << ", " << quote(override) 
	      << ") = " << quote(font) << "\n";
#endif

    return font;
}



//-----------------------------------------------------------------------------
// Setup X fonts
//-----------------------------------------------------------------------------

static StringStringAssoc font_defs;

static void define_font(const AppData& ad,
			const string& name, DDDFont base, 
			const string& override = "")
{
    string font = make_font(ad, base, override);
    const string s1 = upcase(name);
    defineConversionMacro(s1.chars(), font.chars());
    font_defs[name] = font;

    if (ad.show_fonts)
    {
	const string sym =
	  (name == MSTRING_DEFAULT_CHARSET) ?
	  "default" :
	  "@" + name;
	std::cout << sym << "\t" << font << "\n";
    }
}

static void set_db_font(const AppData& ad, XrmDatabase& db,
			const string& line)
{
    XrmPutLineResource(&db, line.chars());

    if (ad.show_fonts)
    {
	string s = line;
	s.gsub(":", ": \\\n   ");
	s.gsub(",", ",\\\n    ");
	std::cout << s << "\n\n";
    }
}

static string define_default_font(const string& font_def)
{
    string s;

    // The canonical way of doing it.
    s += font_def + "=" + MSTRING_DEFAULT_CHARSET + ",";

    // Special cases
    if (string(MSTRING_DEFAULT_CHARSET) != "charset")
    {
	// This happens in Motif 1.1 and LessTif.  Ensure
	// compatibility with other Motif versions.
	s += font_def;
	s += "=charset,";
    }

    return s;
}
	    

static void setup_font_db(const AppData& ad, XrmDatabase& db)
{
    // Default fonts
    string special_fontlist = 
	font_defs[CHARSET_SMALL] + "=" + CHARSET_SMALL + "," +
	font_defs[CHARSET_TT] + "=" + CHARSET_TT + "," +
	font_defs[CHARSET_TB] + "=" + CHARSET_TB + "," +
	font_defs[CHARSET_KEY] + "=" + CHARSET_KEY + "," +
	font_defs[CHARSET_RM] + "=" + CHARSET_RM + "," +
	font_defs[CHARSET_SL] + "=" + CHARSET_SL + "," +
	font_defs[CHARSET_BF] + "=" + CHARSET_BF + "," +
	font_defs[CHARSET_BS] + "=" + CHARSET_BS + "," +
	font_defs[CHARSET_LOGO] + "=" + CHARSET_LOGO + "," +
	font_defs[CHARSET_LLOGO] + "=" + CHARSET_LLOGO + ",";


    string default_fontlist = 
	define_default_font(font_defs[CHARSET_DEFAULT]) + special_fontlist;

    set_db_font(ad, db, string(DDD_CLASS_NAME "*") + 
		XmCFontList + ": " + default_fontlist);

    // Text fonts
    string text_fontlist = 
	define_default_font(font_defs[CHARSET_TEXT]) + special_fontlist;

    set_db_font(ad, db, string(DDD_CLASS_NAME "*XmTextField.") + 
		XmCFontList + ": " + text_fontlist);
    set_db_font(ad, db, string(DDD_CLASS_NAME "*XmText.") + 
		XmCFontList + ": " + text_fontlist);
    set_db_font(ad, db, string(DDD_CLASS_NAME "*XmCommand*XmList.") + 
		XmCFontList + ": " + text_fontlist);

    // Command tool fonts
    string tool_fontlist = 
	define_default_font(font_defs[CHARSET_LIGHT]) + special_fontlist;

    set_db_font(ad, db, 
		string(DDD_CLASS_NAME "*tool_buttons.run.") + 
		XmCFontList + ": " + default_fontlist);
    set_db_font(ad, db, 
		string(DDD_CLASS_NAME "*tool_buttons.break.") +
		XmCFontList + ": " + default_fontlist);
    set_db_font(ad, db, 
		string(DDD_CLASS_NAME "*tool_buttons*") +
		XmCFontList + ": " + tool_fontlist);
}

static void title(const AppData& ad, const string& s)
{
    if (!ad.show_fonts)
	return;

    static bool title_seen = false;

    if (title_seen)
	std::cout << "\n\n";

    std::cout << s << "\n" << replicate('-', s.length()) << "\n\n";

    title_seen = true;
}

static void get_derived_sizes(Dimension size,
			      Dimension& small_size,
			      Dimension& tiny_size,
			      Dimension& llogo_size,
                              bool calcPixel=false)
{
    if (calcPixel)
    {
        // size i pixels
        small_size = (size * 8) / 9;
        tiny_size  = (size * 6) / 9;
        llogo_size = (size * 3) / 2;
    }
    else
    {
        // last digit has to be zero for size in points
        small_size = ((size * 8) / 90) * 10;
        tiny_size  = ((size * 6) / 90) * 10;
        llogo_size = ((size * 3) / 20) * 10;
    }
}

static void setup_x_fonts(const AppData& ad, XrmDatabase& db)
{
    Dimension small_size, tiny_size, llogo_size;
    get_derived_sizes(ad.default_font_size, small_size, tiny_size, llogo_size);

    if (small_size < 80)
	small_size = ad.default_font_size;

    string small_size_s = itostring(small_size);
    string llogo_size_s = itostring(llogo_size);

    // Clear old font defs
    static StringStringAssoc empty;
    font_defs = empty;

    title(ad, "Symbolic font names");

    // Default font
    define_font(ad, CHARSET_DEFAULT, DefaultDDDFont);

    define_font(ad, CHARSET_SMALL, DefaultDDDFont,
		override(PointSize, small_size_s));

    define_font(ad, CHARSET_LIGHT, DefaultDDDFont,
		override(Weight, "medium",
			 override(PointSize, small_size_s)));

    // Text fonts
    define_font(ad, CHARSET_TEXT, FixedWidthDDDFont);

    // Text fonts
    define_font(ad, CHARSET_LOGO, VariableWidthDDDFont,
		override(Weight, "bold"));

    define_font(ad, CHARSET_LLOGO, VariableWidthDDDFont,
		override(Weight, "bold",
			 override(PointSize, llogo_size_s)));

    define_font(ad, CHARSET_RM, VariableWidthDDDFont,
		override(Slant, "r"));

    define_font(ad, CHARSET_SL, VariableWidthDDDFont,
		override(Slant, "*")); // matches `i' and `o'

    define_font(ad, CHARSET_BF, VariableWidthDDDFont,
		override(Weight, "bold",
			 override(Slant, "r")));

    define_font(ad, CHARSET_BS, VariableWidthDDDFont,
		override(Weight, "bold",
			 override(Slant, "*")));

    define_font(ad, CHARSET_TT, FixedWidthDDDFont);

    define_font(ad, CHARSET_TB, FixedWidthDDDFont,
		override(Weight, "bold"));

    define_font(ad, CHARSET_TS, FixedWidthDDDFont,
		override(Slant, "*"));

    define_font(ad, CHARSET_TBS, FixedWidthDDDFont,
		override(Weight, "bold",
			 override(Slant, "*")));

    define_font(ad, CHARSET_KEY, VariableWidthDDDFont,
		override(Weight, "bold"));

    title(ad, "Font resources");

    setup_font_db(ad, db);
}

//-----------------------------------------------------------------------------
// Setup XFT fonts
//-----------------------------------------------------------------------------

static void setup_xft_fonts(AppData& ad, XrmDatabase& db)
{
    if (ad.fixed_width_font_size >=80)
        ad.fixed_width_font_size = 11; // size seem to be in points -> set default

    // according to hints from Joe Nelson
    XrmPutLineResource(&db, "Ddd*source_text_w*renderTable: tt");
    XrmPutLineResource(&db, "Ddd*gdb_w*renderTable: tt");

    XrmPutLineResource(&db, "Ddd*tt*fontType: FONT_IS_XFT");
    XrmPutLineResource(&db, (string("Ddd*tt*fontName: ") + ad.fixed_width_font).chars());
    XrmPutLineResource(&db, (string("Ddd*tt*fontSize: ") + itostring(ad.fixed_width_font_size)).chars());

    XrmPutLineResource(&db, "Ddd*tb*fontType: FONT_IS_XFT");
    XrmPutLineResource(&db, (string("Ddd*tb*fontName: ") + ad.fixed_width_font).chars());
    XrmPutLineResource(&db, (string("Ddd*tb*fontSize: ") + itostring(ad.fixed_width_font_size)).chars());
    XrmPutLineResource(&db, "Ddd*tb*fontStyle: Bold");

    if (ad.variable_width_font_size>=80)
        ad.variable_width_font_size = 11; // size seem to be in points -> set default

    XrmPutLineResource(&db, "Ddd*renderTable: rm,tt,llogo,logo,small,tb,key,bf");

    XrmPutLineResource(&db, "Ddd*rm*fontType: FONT_IS_XFT");
    XrmPutLineResource(&db, (string("Ddd*rm*fontName: ") + ad.variable_width_font).chars());
    XrmPutLineResource(&db, (string("Ddd*rm*fontSize: ") + itostring(ad.variable_width_font_size)).chars());

    XrmPutLineResource(&db, "Ddd*bf*fontType: FONT_IS_XFT");
    XrmPutLineResource(&db, (string("Ddd*bf*fontName: ") + ad.variable_width_font).chars());
    XrmPutLineResource(&db, (string("Ddd*bf*fontSize: ") + itostring(ad.variable_width_font_size)).chars());
    XrmPutLineResource(&db, "Ddd*bf*fontStyle: Bold");

    XrmPutLineResource(&db, "Ddd*small*fontType: FONT_IS_XFT");
    XrmPutLineResource(&db, (string("Ddd*small*fontName: ") + ad.variable_width_font).chars());
    XrmPutLineResource(&db, (string("Ddd*small*fontSize: ") + itostring(ad.variable_width_font_size*.8)).chars());

    XrmPutLineResource(&db, "Ddd*llogo*fontType: FONT_IS_XFT");
    XrmPutLineResource(&db, (string("Ddd*llogo*fontName: ") + ad.variable_width_font).chars());
    XrmPutLineResource(&db, (string("Ddd*llogo*fontSize: ") + itostring(ad.variable_width_font_size*2)).chars());
    XrmPutLineResource(&db, (string("Ddd*llogo*fontStyle: Bold").chars()));

    XrmPutLineResource(&db, "Ddd*logo*fontType: FONT_IS_XFT");
    XrmPutLineResource(&db, (string("Ddd*logo*fontName: ") + ad.variable_width_font).chars() );
    XrmPutLineResource(&db, (string("Ddd*logo*fontSize: ") + itostring(ad.variable_width_font_size*1.2)).chars());
    XrmPutLineResource(&db, "Ddd*logo*fontStyle: Bold");

    XrmPutLineResource(&db, "Ddd*key*fontType: FONT_IS_XFT");
    XrmPutLineResource(&db, (string("Ddd*key*fontName: ") + ad.variable_width_font).chars());
    XrmPutLineResource(&db, (string("Ddd*key*fontSize: ") + itostring(ad.variable_width_font_size)).chars());
    XrmPutLineResource(&db, "Ddd*key*fontStyle: Bold");
}

string make_xftfont(const AppData& ad, DDDFont base)
{
    switch(base)
    {
        case VariableWidthDDDFont:
            return string(ad.variable_width_font) +string(":size=") + itostring(ad.variable_width_font_size);

        case DataDDDFont:
            return string(ad.data_font) +string(":size=") + itostring(ad.data_font_size);

        default:
        case FixedWidthDDDFont:
            return string(ad.fixed_width_font) +string(":size=") + itostring(ad.fixed_width_font_size);
    }
}



//-----------------------------------------------------------------------------
// Set VSL font resources
//-----------------------------------------------------------------------------

void replace_vsl_xftfont(string& defs, const string& func,
			     const string& font, const Dimension size, const string& override = "")
{
    string fontname = quote(font+string(":size=")+itostring(size)+override);
    defs += "#pragma replace " + func + "\n" + 
	func + "(box) = font(box, " + fontname + ");\n";
}

void replace_vsl_font(string& defs, const string& func,
			     const AppData& ad, const string& override = "",
			     DDDFont font = DataDDDFont)
{
    string fontname = quote(make_font(ad, font, override));
    defs += "#pragma replace " + func + "\n" + 
	func + "(box) = font(box, " + fontname + ");\n";
}

static void setup_vsl_fonts(AppData& ad)
{
    Dimension small_size, tiny_size, llogo_size;
#ifdef HAVE_FREETYPE
    if (ad.data_font_size >=80)
        ad.data_font_size = 11;

    get_derived_sizes(ad.data_font_size, small_size, tiny_size, llogo_size, true);

    static string defs; // defs.chars() is used in AppData
    defs = "";

    title(ad, "VSL defs");

    replace_vsl_xftfont(defs, "rm", ad.data_font, ad.data_font_size);
    replace_vsl_xftfont(defs, "bf", ad.data_font, ad.data_font_size, ":weight=bold");
    replace_vsl_xftfont(defs, "it", ad.data_font, ad.data_font_size, ":slant=italic");
    replace_vsl_xftfont(defs, "bf", ad.data_font, ad.data_font_size, ":weight=bold:slant=italic");

    replace_vsl_xftfont(defs, "small_rm", ad.data_font, small_size);
    replace_vsl_xftfont(defs, "small_bf", ad.data_font, small_size, ":weight=bold");
    replace_vsl_xftfont(defs, "small_it", ad.data_font, small_size, ":slant=italic");
    replace_vsl_xftfont(defs, "small_bf", ad.data_font, small_size, ":weight=bold:slant=italic");

    replace_vsl_xftfont(defs, "tiny_rm", ad.data_font, tiny_size);
    replace_vsl_xftfont(defs, "tiny_bf", ad.data_font, tiny_size, ":weight=bold");
    replace_vsl_xftfont(defs, "tiny_it", ad.data_font, tiny_size, ":slant=italic");
    replace_vsl_xftfont(defs, "tiny_bf", ad.data_font, tiny_size, ":weight=bold:slant=italic");
#else
    get_derived_sizes(ad.data_font_size, small_size, tiny_size, llogo_size);

    string small_size_s = itostring(small_size);
    string tiny_size_s  = itostring(tiny_size);

    static string defs;
    defs = "";

    title(ad, "VSL defs");

    replace_vsl_font(defs, "rm", ad);
    replace_vsl_font(defs, "bf", ad, 
		     override(Weight, "bold"));
    replace_vsl_font(defs, "it", ad, 
		     override(Slant, "*"));
    replace_vsl_font(defs, "bf", ad, 
		     override(Weight, "bold",
			      override(Slant, "*")));

    replace_vsl_font(defs, "small_rm", ad, 
		     override(PointSize, small_size_s));
    replace_vsl_font(defs, "small_bf", ad, 
		     override(Weight, "bold", 
			      override(PointSize, small_size_s)));
    replace_vsl_font(defs, "small_it", ad, 
		     override(Slant, "*", 
			      override(PointSize, small_size_s)));
    replace_vsl_font(defs, "small_bf", ad, 
		     override(Weight, "bold", 
			      override(Slant, "*", 
				       override(PointSize, small_size_s))));

    replace_vsl_font(defs, "tiny_rm", ad, 
		     override(PointSize, tiny_size_s), VariableWidthDDDFont);
    replace_vsl_font(defs, "tiny_bf", ad, 
		     override(Weight, "bold", 
			      override(PointSize, tiny_size_s)), 
		     VariableWidthDDDFont);
    replace_vsl_font(defs, "tiny_it", ad, 
		     override(Slant, "*", 
			      override(PointSize, tiny_size_s)),
		     VariableWidthDDDFont);
    replace_vsl_font(defs, "tiny_bf", ad, 
		     override(Weight, "bold", 
			      override(Slant, "*", 
				       override(PointSize, tiny_size_s))),
		     VariableWidthDDDFont);
#endif

    if (ad.show_fonts)
	std::cout << defs;

    defs += ad.vsl_base_defs;
    ad.vsl_base_defs = defs.chars();
}

void setup_fonts(AppData& ad, XrmDatabase db)
{
    XrmDatabase db2 = db;
#ifdef HAVE_FREETYPE
    setup_xft_fonts(ad, db2);
#else
    setup_x_fonts(ad, db2);
#endif
    assert(db == db2);

    setup_vsl_fonts(ad);
}



//-----------------------------------------------------------------------------
// Handle font resources
//-----------------------------------------------------------------------------

// Simplify font specs
static string simplify_font(const AppData& ad, DDDFont font, 
			    const string& source)
{
    string s;

    for (FontComponent n = AllComponents; n >= Foundry; n--)
    {
	string c = component(source, n);
	if (s.empty() && c == component(ad, font, n))
	{
	    // Default setting -- ignore
	}
	else
	{
	    s.prepend("-" + c);
	}
    }

    if (s.contains("-*-", 0))
	s = s.after("-*-");

    if (s.empty())
	s = component(ad, font, Family);
    if (!s.contains('-')) {
	s += '-';
	s += component(ad, font, Weight);
    }

#if 0
    std::clog << "simplify_font(" << font_type(font) << ", " 
	      << quote(source) << ") = " << quote(s) << "\n";
#endif

    return s;
}

// Set a new font resource
void set_font(DDDFont font, const string& name)
{
    switch (font)
    {
    case DefaultDDDFont:
    {
	static string s;
	s = name;
	app_data.default_font = s.chars();
	break;
    }
    case VariableWidthDDDFont:
    {
	static string s;
	s = name;
	app_data.variable_width_font = s.chars();
	break;
    }
    case FixedWidthDDDFont:
    {
	static string s;
	s = name;
	app_data.fixed_width_font = s.chars();
	break;
    }
    case DataDDDFont:
    {
	static string s;
	s = name;
	app_data.data_font = s.chars();
	break;
    }
    default:
	assert(0);
	::abort();
    }
}

// Set a new font resource
static void set_font_size(DDDFont font, int size)
{
    switch (font)
    {
    case DefaultDDDFont:
	app_data.default_font_size = size;
	break;
    case VariableWidthDDDFont:
	app_data.variable_width_font_size = size;
	break;
    case FixedWidthDDDFont:
	app_data.fixed_width_font_size = size;
	break;
    case DataDDDFont:
	app_data.data_font_size = size;
	break;
    default:
	assert(0);
	::abort();
    }
}


void SetFontNameCB(Widget w, XtPointer client_data, XtPointer)
{
    DDDFont font = (DDDFont) (long) client_data;
    String s = XmTextFieldGetString(w);
    set_font(font, s);
    XtFree(s);

    update_reset_preferences();
}

void SetXTFFontNameCB(Widget w, XtPointer client_data, XtPointer)
{
    DDDFont font = (DDDFont) (long) client_data;
    String s = XtName(w);
    set_font(font, s);

    update_reset_preferences();
}

void SetFontSizeCB(Widget w, XtPointer client_data, XtPointer)
{
    DDDFont font = (DDDFont) (long) client_data;
    String s = XmTextFieldGetString(w);
    set_font_size(font, atoi(s));
    XtFree(s);

    update_reset_preferences();
}

#ifdef HAVE_FREETYPE
std::vector<string> GetFixedWithFonts()
{
    std::vector<string> fontlist;

    FcInit();

    FcPattern *pattern = FcPatternCreate();
    FcObjectSet *os = FcObjectSetBuild(FC_FAMILY, FC_STYLE,  FC_SPACING, FC_CHARSET, NULL);

    FcFontSet *fontSet = FcFontList(NULL, pattern, os);
    FcObjectSetDestroy(os);

    if (fontSet == nullptr)
        return fontlist;

    const FcCharSet *englishCharset = FcLangGetCharSet((const FcChar8 *)"en");
    for (int i = 0; i < fontSet->nfont; ++i)
    {
        FcPattern *font = fontSet->fonts[i];
        FcChar8 *family, *style ;
        int spacing;
        FcCharSet *charset;

        if (FcPatternGetString(font, FC_FAMILY, 0, &family) == FcResultMatch &&
            FcPatternGetString(font, FC_STYLE, 0, &style) == FcResultMatch &&
            FcPatternGetInteger(font, FC_SPACING, 0, &spacing) == FcResultMatch &&
            FcPatternGetCharSet(font, FC_CHARSET, 0, &charset) == FcResultMatch &&
            spacing == FC_MONO &&
            (strcmp((char*)style, "Medium") == 0 || strcmp((char*)style, "Regular") == 0) &&
            (FcCharSetIsSubset(englishCharset, charset)))
        {
            fontlist.push_back(string((char*)family));
        }
    }

    FcFontSetDestroy(fontSet);

    return fontlist;
}

std::vector<string> GetVarWithFonts()
{
    std::vector<string> fontlist;

    std::vector<string> oklist = {"Arial", "Chandas", "DejaVu Sans", "Free Sans", "Kalimati", "Liberation Sans",
        "Luxi Sans", "Loma", "Nimbus Sans", "Noto Sans", "Padauk", "Quicksand", "Sawasdee", "Ubuntu", "Umpush",
        "Verdana", "Waree"};

    FcInit();

    FcPattern *pattern = FcPatternCreate();
    FcObjectSet *os = FcObjectSetBuild(FC_FAMILY, FC_STYLE, FC_LANG, NULL);

    FcFontSet *fontSet = FcFontList(NULL, pattern, os);
    FcObjectSetDestroy(os);

    if (fontSet)
    {
        for (int i = 0; i < fontSet->nfont; ++i)
        {
            FcPattern *font = fontSet->fonts[i];
            FcChar8 *family, *style;
            FcLangSet *langset;

            if (FcPatternGetString(font, FC_FAMILY, 0, &family) == FcResultMatch &&
                FcPatternGetString(font, FC_STYLE, 0, &style) == FcResultMatch &&
                FcPatternGetLangSet(font, FC_LANG, 0, &langset ) == FcResultMatch &&
                FcLangSetHasLang(langset, (const FcChar8*)"de") == FcLangEqual &&
                (strcmp((char*)style, "Medium") == 0 || strcmp((char*)style, "Regular") == 0)
            )
            {
                if(std::find(oklist.begin(), oklist.end(), string((char*)family)) != oklist.end())
                    fontlist.push_back(string((char*)family));
            }
        }

        FcFontSetDestroy(fontSet);
    }

    return fontlist;
}


static std::vector<string> fixedfonts;
static std::vector<string> varfonts;

static std::vector<MMDesc> varw_fonts;
static std::vector<MMDesc> varw_fonts_menu;
static std::vector<MMDesc> fixedw_fonts;
static std::vector<MMDesc> fixedw_fonts_menu;
static std::vector<MMDesc> data_fonts;
static std::vector<MMDesc> data_font_menu;

static Widget varwFontWidget;
static Widget fixedwFontWidget;
static Widget dataFontWidget;

std::vector<MMDesc> CreateFontSelectMenu(Widget *font_sizes)
{
    fixedfonts = GetFixedWithFonts();
    varfonts = GetVarWithFonts();

    // variable width fonts
    varw_fonts.clear();
    for (string &font : varfonts)
        varw_fonts.push_back({ font.chars(), MMPush, { SetXTFFontNameCB, XtPointer(VariableWidthDDDFont) }, 0, 0, 0, 0});
    varw_fonts.push_back(MMEnd);

    varw_fonts_menu.clear();
    varw_fonts_menu.push_back({ "name",   MMOptionMenu , MMNoCB, &varw_fonts[0], &varwFontWidget, 0, 0 });
    varw_fonts_menu.push_back({ "size",   MMTextField, { SetFontSizeCB, XtPointer(VariableWidthDDDFont) }, 0, &font_sizes[int(VariableWidthDDDFont)], 0, 0 });
    varw_fonts_menu.push_back(MMEnd);

    // fixed width fonts
    fixedw_fonts.clear();
    for (string &font : fixedfonts)
        fixedw_fonts.push_back({ font.chars(), MMPush, { SetXTFFontNameCB, XtPointer(FixedWidthDDDFont) }, 0, 0, 0, 0});
    fixedw_fonts.push_back(MMEnd);

    fixedw_fonts_menu.clear();
    fixedw_fonts_menu.push_back({ "name",   MMOptionMenu , MMNoCB, &fixedw_fonts[0], &fixedwFontWidget, 0, 0 });
    fixedw_fonts_menu.push_back({ "size",   MMTextField, { SetFontSizeCB, XtPointer(FixedWidthDDDFont) }, 0, &font_sizes[int(FixedWidthDDDFont)], 0, 0 });
    fixedw_fonts_menu.push_back(MMEnd);

    // data fonts
    data_fonts.clear();
    for (string &font : fixedfonts)
        data_fonts.push_back({ font.chars(), MMPush, { SetXTFFontNameCB, XtPointer(DataDDDFont) }, 0, 0, 0, 0});
    data_fonts.push_back(MMEnd);

    data_font_menu.clear();
    data_font_menu.push_back({ "name",   MMOptionMenu , MMNoCB, &data_fonts[0], &dataFontWidget, 0, 0 });
    data_font_menu.push_back({ "size",   MMTextField, { SetFontSizeCB, XtPointer(DataDDDFont) }, 0, &font_sizes[int(DataDDDFont)], 0, 0 });
    data_font_menu.push_back(MMEnd);


    std::vector<MMDesc> menu;
    menu.push_back({ "variableWidth", MMPanel,  MMNoCB, &varw_fonts_menu[0], 0, 0, 0 });
    menu.push_back({ "fixedWidth",    MMPanel,  MMNoCB, &fixedw_fonts_menu[0], 0, 0, 0 });
    menu.push_back({ "data",          MMPanel,  MMNoCB, &data_font_menu[0], 0, 0, 0 });
    menu.push_back(MMEnd);

    return menu;
}

void SetActivatedFonts(const AppData& ad)
{
    // variable width font
    for (MMDesc &desc : varw_fonts)
        if (desc.name!=nullptr && strcmp(desc.name, ad.variable_width_font)==0 && desc.widget!=nullptr)
            XtVaSetValues(varwFontWidget, XmNmenuHistory, desc.widget, XtPointer(0));

    // fixed width font
    for (MMDesc &desc : fixedw_fonts)
        if (desc.name!=nullptr && strcmp(desc.name, ad.fixed_width_font)==0 && desc.widget!=nullptr)
            XtVaSetValues(fixedwFontWidget, XmNmenuHistory, desc.widget, XtPointer(0));

    // data font
    for (MMDesc &desc : data_fonts)
        if (desc.name!=nullptr && strcmp(desc.name, ad.data_font)==0 && desc.widget!=nullptr)
            XtVaSetValues(dataFontWidget, XmNmenuHistory, desc.widget, XtPointer(0));
}
#endif

//-----------------------------------------------------------------------------
// Font browser
//-----------------------------------------------------------------------------

struct FontSelectInfo {
    DDDFont font;
    Widget text;
};

static void gdbDeleteFontSelectAgent(XtPointer client_data, XtIntervalId *)
{
    // Delete agent after use
    Agent *font_select_agent = (Agent *)client_data;
    delete font_select_agent;
}

static string output_buffer;

static void FontSelectionErrorHP(Agent *, void *, void *call_data)
{
    DataLength *input = (DataLength *)call_data;
    output_buffer += string(input->data, input->length);
    while (output_buffer.contains('\n'))
    {
	set_status(output_buffer.before('\n'));
	output_buffer = output_buffer.after('\n');
    }
    if (!output_buffer.empty())
	set_status(output_buffer);
}

static void DeleteAgentHP(Agent *agent, void *client_data, void *)
{
    FontSelectInfo *info = (FontSelectInfo *)client_data;

    // Agent has died -- delete it
    XtAppAddTimeOut(XtWidgetToApplicationContext(gdb_w), 0, 
		    gdbDeleteFontSelectAgent, 
		    XtPointer(agent));

    // Destroy the text
    DestroyWhenIdle(info->text);

    if (!output_buffer.empty())
	set_status("");
}

static void process_font(DDDFont font, string fontspec)
{
    string sz = component(fontspec, PointSize);
    if (sz != "*" && sz != "0")
	set_font_size(font, atoi(sz.chars()));

    fontspec.gsub('*', ' ');
    set_font(font, simplify_font(app_data, font, 
				 make_font(app_data, font, fontspec)));

    update_options();
}

// Handle `Quit' button in xfontsel
static void FontSelectionDoneHP(Agent *agent, void *client_data, 
				void *call_data)
{
    FontSelectInfo *info = (FontSelectInfo *)client_data;

    // Fetch string from font selector
    DataLength *d = (DataLength *)call_data;
    string fontspec(d->data, d->length);
    strip_space(fontspec);

    if (!fontspec.contains('-', 0))
    {
	// Treat as error
	FontSelectionErrorHP(agent, client_data, call_data);
	return;
    }

    process_font(info->font, fontspec);
}


static void GotSelectionCB(Widget w, XtPointer client_data,
			   Atom *, Atom *type, XtPointer value,
			   unsigned long *length, int *format)
{
    FontSelectInfo *info = (FontSelectInfo *)client_data;

    if (*type == None)
	return;			// Could not fetch selection

    if (*type != XA_STRING)
    {
	XtFree((char *)value);
	return;			// Not a string
    }

    if (*format != 8)
    {
	XtFree((char *)value);
	return;			// No 8-bit-string
    }

    string s((String)value, *length);
    if (s.contains('\0'))
	s = s.before('\0');
    XtFree((char *)value);

    if (s.contains("-", 0) && !s.contains('\n') && 
	s.freq('-') == AllComponents)
    {
	process_font(info->font, s);
    }

    XmTextSetString(w, XMST(s.chars()));

    // Get the selection again.
    // This will fail if we have multiple font selectors (FIXME).
    TextSetSelection(w, 0, s.length(), 
		     XtLastTimestampProcessed(XtDisplay(w)));
}

// Handle `Select' button in xfontsel
static void SelectionLostCB(Widget w, XtPointer client_data, XtPointer)
{
    FontSelectInfo *info = (FontSelectInfo *)client_data;
    assert(info->text == w);

    XtGetSelectionValue(w, XA_PRIMARY, XA_STRING, GotSelectionCB,
			XtPointer(info), 
			XtLastTimestampProcessed(XtDisplay(w)));
}


// Browse fonts
void BrowseFontCB(Widget w, XtPointer client_data, XtPointer call_data)
{
    Time tm = CurrentTime;
    XmPushButtonCallbackStruct *cbs = (XmPushButtonCallbackStruct *)call_data;
    if (cbs && cbs->event)
	tm = time(cbs->event);

    DDDFont font = (DDDFont) (long) client_data;

    StatusDelay delay("Invoking " + font_type(font) + " selector");

    string cmd = app_data.font_select_command;
    cmd.gsub("@FONT@", make_font(app_data, DefaultDDDFont));
    string type = font_type(font);
    type[0] = toupper(type[0]);
    cmd.gsub("@TYPE@", type);
    cmd = sh_command(cmd, true);

    // Create a TextField to fetch the selection
    FontSelectInfo *info = new FontSelectInfo;
    info->text = XmCreateText(XtParent(w), XMST("text"), 0, 0);
    info->font = font;

    XtRealizeWidget(info->text);

    const string text = "dummy";
    XmTextSetString(info->text, XMST(text.chars()));
    TextSetSelection(info->text, 0, text.length(), tm);
    XtAddCallback(info->text, XmNlosePrimaryCallback, 
		  SelectionLostCB, XtPointer(info));

    // Invoke a font selector
    LiterateAgent *font_select_agent = 
	new LiterateAgent(XtWidgetToApplicationContext(w), cmd);

    output_buffer = "";

    font_select_agent->removeAllHandlers(Died);
    font_select_agent->addHandler(Died,
				  DeleteAgentHP, (void *)info);
    font_select_agent->addHandler(Input,
				  FontSelectionDoneHP, (void *)info);
    font_select_agent->addHandler(Error,
				  FontSelectionErrorHP, (void *)info);
    font_select_agent->start();
}
