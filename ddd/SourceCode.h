// $Id$ -*- C++ -*-
// buffer for the current source code

// Copyright (C) 1997 Technische Universitaet Braunschweig, Germany.
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

#ifndef _DDD_SourceCode_h
#define _DDD_SourceCode_h
#include <vector>
#include <map>

// Motif includes
#include <Xm/Xm.h>

// Misc includes
#include "base/strclass.h"
#include "base/cwd.h"
#include "base/tabs.h"
#include "base/basename.h"

// DDD includes
#include "GDBAgent.h"


//-----------------------------------------------------------------------------
extern GDBAgent* gdb;

class SourceCode
{
public:
    // Source origins
    enum SourceOrigin { ORIGIN_LOCAL, ORIGIN_REMOTE, ORIGIN_GDB, ORIGIN_NONE };

private:
    // The current source text.
    string current_source = "";

    // Tab width
    int tab_width = DEFAULT_TAB_WIDTH;

    // The indenting amounts
    int source_indent_amount = 4;         // Source
    int line_indent_amount = 4;           // Extra columns for line numbers
    int script_indent_amount = 4;         // Minimum for scripts

    // File attributes
    string current_file_name = "";
    int line_count = 0;
    int char_count = 0;
    std::vector<XmTextPosition> textpos_of_line;
    std::vector<unsigned int> bytepos_of_line;

    // The origin of the current source text.
    SourceOrigin current_origin = ORIGIN_NONE;

    // Check whether source files and code are to be cached
    bool cache_source_files = true;

    // source file caches
    struct FileCacheEntry
    {
        string text;
        SourceOrigin origin;
        string file_name; // File name of current source (for JDB)
    };
    std::map<string, FileCacheEntry> filecache;
    std::map<string, string> source_name_cache;

    bool display_line_numbers = false;              // Display line numbers?

    Widget source_text_w = 0;

    // Files listed as erroneous
    std::vector<string> bad_files;

    bool new_bad_file(const string& file_name);
    void post_file_error(const string& file_name,
                                const string& text, const _XtString name = 0,
                                Widget origin = 0);
    void post_file_warning(const string& file_name,
                                  const string& text, const _XtString name = 0,
                                  Widget origin = 0);
    // Read source text
    String read_local(const string& file_name, long& length, bool silent);
    String read_remote(const string& file_name, long& length, bool silent);
    String read_class(const string& class_name, string& file_name, SourceOrigin& origin,
                             long& length, bool silent);
    String read_from_gdb(const string& source_name, long& length, bool silent);
    String read_indented(string& file_name, long& length, SourceOrigin& origin, bool silent);

public:

    // The current directory
    string current_pwd = cwd();

    // access functions for source
    const string& get_source() { return current_source; }
    unsigned int get_length() { return current_source.length(); }
    const subString get_source_at(int pos, int length);


    // access functions for file attributes
    const string& get_filename()  { return current_file_name; }
    void reset_filename() { current_file_name = ""; }
    int get_num_lines() {return line_count+1; }
    int get_num_characters() {return char_count; }
    SourceOrigin get_origin() { return current_origin; }
    XmTextPosition pos_of_line(int line);
    int line_of_pos(XmTextPosition pos);
    int line_of_bytepos(int pos);
    XmTextPosition startofline_at_pos(XmTextPosition pos);
    XmTextPosition endofline_at_pos(XmTextPosition pos);
    const subString get_source_line(int line);
    string get_source_lineASCII(int line);

    int charpos_to_bytepos(XmTextPosition pos);
    XmTextPosition bytepos_to_charpos(int pos);


    // Read source text
    int read_current(string& file_name, bool force_reload, bool silent, Widget w);

    bool set_tab_width(int width);
    bool set_indent(int source_indent, int script_indent);
    bool set_display_line_numbers(bool set);

    // Return current breakpoint indent amount.  If POS is given, add
    // the whitespace from POS.
    int calculate_indent(int pos = -1);

    // True iff we have some source text
    bool have_source() { return current_source.length() != 0; }

    // Caches
    void clear_file_cache();
    void set_caches(bool set)
    {
        if (set==cache_source_files)
            return;

        cache_source_files = set;
        if (cache_source_files==false)
            clear_file_cache();
    }

    bool get_source_from_file(const string& file_name, string& source_name)
    {
        auto search = source_name_cache.find(file_name);
        if (search==source_name_cache.end())
            return false;

        source_name = search->second;
        return true;
    }

    // Return current source name (name under this source is known to GDB)
    string get_source_name(string filename = "");
    string current_source_name();

    string full_path(string file);

    bool base_matches(const string& file1, const string& file2)
    {
        return string(basename(file1.chars())) == string(basename(file2.chars()));
    }

};

#endif // _DDD_SourceCode_h
// DON'T ADD ANYTHING BEHIND THIS #endif




























