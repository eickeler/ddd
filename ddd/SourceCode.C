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

char SourceCode_rcsid[] =
    "$Id$";

//-----------------------------------------------------------------------------
#include "config.h"

#include "SourceCode.h"

// DDD stuff
#include "AppData.h"
#include "Command.h"
#include "assert.h"
#include "base/basename.h"
#include "base/cook.h"
#include "dbx-lookup.h"
#include "file.h"
#include "java.h"
#include "base/misc.h"
#include "post.h"
#include "regexps.h"
#include "shell.h"
#include "status.h"


// System stuff
extern "C" {
#include <sys/types.h>
#include <sys/stat.h>
}
#include <stdio.h>



static const int MAX_INDENT = 64;
static const int MAX_LINE_NUMBER_WIDTH = 6;


// Test for regular file - see stat(3)
#ifndef S_ISREG
#define S_ISREG(m) (((m) & S_IFMT) == S_IFREG)
#endif

bool utf8toUnicode(wchar_t &unicode, const char *text, int &pos, const int length)
{
    const unsigned char *utext = (const unsigned char *)text;
    unicode = 0;
    if (utext==nullptr || pos>=length || utext[pos] == 0)
        return false;

    if ((utext[pos] & 0x80) == 0)
    {
        // U+0000-U+007F
        unicode = utext[pos];
        pos += 1;
        return true;
    }

    if (pos+1>=length || utext[pos+1] == 0)
        return false;

    if ((utext[pos] & 0xe0) == 0xc0 && (utext[pos+1] & 0xc0) == 0x80)
    {
        // U+0080-U+07FF
        unicode = ((utext[pos] & 0x1f) << 6) | (utext[pos+1] & 0x3f);
        pos += 2;
        return true;
    }

    if (pos+2>=length || utext[pos+2] == 0)
        return false;

    if ((utext[pos] & 0xf0) == 0xe0 && (utext[pos+1] & 0xc0) == 0x80 && (utext[pos+2] & 0xc0) == 0x80)
    {
        // U+0800-U+FFFF
        unicode = ((utext[pos] & 0x1f) << 12) | ((utext[pos+1] & 0x3f) << 6) | (utext[pos+2] & 0x3f);
        pos += 3;
        return true;
    }

    if (pos+2>=length || utext[pos+2] == 0)
        return false;

    if ((utext[pos] & 0xf8) == 0xf0 && (utext[pos+1] & 0xc0) == 0x80 && (utext[pos+2] & 0xc0) == 0x80 && (utext[pos+3] & 0xc0) == 0x80)
    {
        // U+10000-U+10FFFF
        unicode = ((utext[pos] & 0x1f) << 18) | ((utext[pos+1] & 0x3f) << 12) | ((utext[pos+2] & 0x3f) << 6) | (utext[pos+3] & 0x3f);
        pos += 4;
        return true;
    }

    return false;
}

/*! Measures the indent of the specified \c line.
 * If the line number is negative, the default indent is returned
 * \param[in] line line number in the range 1..number of lines
 * \return returns the amount of indention
 */
int SourceCode::calculate_indent(int line)
{
    int indent = source_indent_amount;

    if (display_line_numbers)
        indent += line_indent_amount;

    // Set a minimum indentation for scripting languages
    if (gdb->requires_script_indent())
        indent = max(indent, script_indent_amount);

    // Make sure indentation stays within reasonable bounds
    indent = min(max(indent, 0), MAX_INDENT);

    line --; // convert from extenal 1.. to internal 0..
    if (line < 0 || line >= int(bytepos_of_line.size()))
        return indent;

    const string& text = current_source;

    int bpos = bytepos_of_line[line] + indent;
    while (bpos < int(text.length()) && text[bpos] == ' ')
    {
        bpos++;
        indent++;
    }

    return indent;
}

// ***************************************************************************
//
// Return the normalized full path of FILE
string SourceCode::full_path(string file)
{
    /* Chris van Engelen <engelen@lucent.com>, Jul 10, 1997
     *
     * The regular expression is used to remove parts from the full path
     * which look like "/aap/../". However, it should ***NOT*** remove
     * the sequence "/../../" from the path, obviously ! On the other
     * hand, sequences like "/.tmpdir.test/../" should be removed.
     * Therefore, the regular expression reads now like:
     *
     * - forward slash
     * - zero or more  characters other than forward slash (dot is allowed)
     * - any character other than forward slash or dot: this makes sure that
     *   a sequence like "/../../" is not modified.
     * - forward slash, two dots, and the final forward slash.
     *
     * The only valid patterns which are not normalized are patterns ending
     * in a dot: too bad, you can't win them all.
     */

#if RUNTIME_REGEX
    static regex rxdotdot("/[^/]*[^/.]/\\.\\./");
#endif

    file += '/';

    if (!file.contains('/', 0))
        file = current_pwd + "/" + file;

    /* CvE, Jul 10, 1997
     *
     * Repeatedly remove patterns like /dir1/../ from the file name.
     * Note that a number of /../ patterns may follow each other, like
     * in "/dir1/dir1/dir3/../../../"
     */
    unsigned int file_length = file.length();
    unsigned int prev_file_length;
    do {
        prev_file_length = file_length;
        file.gsub(rxdotdot, "/");
        file_length = file.length();
    } while (file_length != prev_file_length);

    /* CvE, Jul 10, 1997
     *
     * Repeatedly remove pattern /./ from the file name.
     * Note that a number of /./ patterns may follow each other.
     * Note that if the first parameter of gsub is a C-string,
     * the pattern is not regarded to be a regular expression,
     * so the dot in the pattern does not need to be escaped!
     */
    file_length = file.length();
    do {
        prev_file_length = file_length;
        file.gsub("/./", "/");
        file_length = file.length();
    } while (file_length != prev_file_length);

    // Don't do this - it breaks file access on Cygwin, where
    // `//c/foo/bar' is translated to `c:\foo\bar'.
    // file.gsub("//", "/");

    if (file.contains('/', -1))
        file = file.before(int(file.length() - 1));

    return file;
}

//-----------------------------------------------------------------------
// Error handling
//-----------------------------------------------------------------------

bool SourceCode::new_bad_file(const string& file_name)
{
    for (int i = 0; i < int(bad_files.size()); i++)
        if (file_name == bad_files[i])
            return false;
    bad_files.push_back(file_name);
    return true;
}

void SourceCode::post_file_error(const string& file_name,
                                 const string& text, const _XtString name,
                                 Widget origin)
{
    if (new_bad_file(file_name))
        post_error(text, name, origin);
}

void SourceCode::post_file_warning(const string& file_name,
                                   const string& text, const _XtString name,
                                   Widget origin)
{
    if (new_bad_file(file_name))
        post_warning(text, name, origin);
}

//-----------------------------------------------------------------------
// Read file
//-----------------------------------------------------------------------

// Read local file from FILE_NAME
String SourceCode::read_local(const string& file_name, long& length,
                              bool silent)
{
    StatusDelay delay("Reading file " + quote(file_name));
    length = 0;

    // Make sure the file is a regular text file and open it
    int fd;
    if ((fd = open(file_name.chars(), O_RDONLY)) < 0)
    {
        delay.outcome = strerror(errno);
        //if (!silent)
        //    post_file_error(file_name,
        //                    file_name + ": " + delay.outcome,
        //                    "source_file_error", source_text_w);
        return 0;
    }

    struct stat statb;
    if (fstat(fd, &statb) < 0)
    {
        delay.outcome = strerror(errno);
        if (!silent)
            post_file_error(file_name,
                            file_name + ": " + delay.outcome,
                            "source_file_error", source_text_w);
        return 0;
    }

    // Avoid loading from directory, socket, device, or otherwise.
    if (!S_ISREG(statb.st_mode))
    {
        delay.outcome = "not a regular file";
        if (!silent)
            post_file_error(file_name,
                            file_name + ": " + delay.outcome,
                            "source_file_error", source_text_w);
        return 0;
    }

    // Put the contents of the file in the Text widget by allocating
    // enough space for the entire file and reading the file into the
    // allocated space.
    char* text = XtMalloc(unsigned(statb.st_size + 1));
    if ((length = read(fd, text, statb.st_size)) != statb.st_size)
    {
        delay.outcome = "truncated";
        if (!silent)
            post_file_error(file_name,
                            file_name + ": " + delay.outcome,
                            "source_trunc_error", source_text_w);
    }
    close(fd);

    text[statb.st_size] = '\0'; // be sure to null-terminate

    if (statb.st_size == 0)
    {
        delay.outcome = "empty file";
        if (!silent)
            post_file_warning(file_name,
                              file_name + ": " + delay.outcome,
                              "source_empty_warning", source_text_w);
    }

    return text;
}


// Read (possibly remote) file FILE_NAME; a little slower
String SourceCode::read_remote(const string& file_name, long& length,
                               bool silent)
{
    StatusDelay delay("Reading file " +
                      quote(file_name) + " from " + gdb_host);
    length = 0;

    string cat_command = sh_command("cat " + file_name);

    Agent cat(cat_command);
    cat.start();

    FILE *fp = cat.inputfp();
    if (fp == 0)
    {
        delay.outcome = "failed";
        return 0;
    }

    String text = XtMalloc(1);

    do {
        text = XtRealloc(text, length + BUFSIZ + 1);
        length += fread(text + length, sizeof(char), BUFSIZ, fp);
    } while (!feof(fp));

    text[length] = '\0';  // be sure to null-terminate

    if (length == 0)
    {
        if (!silent)
            post_file_error(file_name,
                            "Cannot access remote file " + quote(file_name),
                            "remote_file_error", source_text_w);
        delay.outcome = "failed";
    }

    return text;
}

// Read class CLASS_NAME
String SourceCode::read_class(const string& class_name,
                              string& file_name, SourceOrigin& origin,
                              long& length, bool silent)
{
    StatusDelay delay("Loading class " + quote(class_name));

    String text = 0;
    length = 0;

    file_name = java_class_file(class_name);

    if (!file_name.empty())
    {
        if (remote_gdb())
            text = read_remote(file_name, length, true);
        else
        {
            file_name = full_path(file_name);
            text = read_local(file_name, length, true);
        }
    }

    if (text != 0 && length != 0)
    {
        // Save class name for further reference
        source_name_cache[file_name] = class_name;
        origin = remote_gdb() ? ORIGIN_REMOTE : ORIGIN_LOCAL;
        return text;
    }
    else
    {
        // Could not load class
        file_name = class_name;
        origin = ORIGIN_NONE;
        delay.outcome = "failed";
        if (!silent)
            post_file_error(class_name,
                            "Cannot access class " + quote(class_name),
                            "class_error", source_text_w);

        return 0;
    }
}

#define HUGE_LINE_NUMBER "1000000"

// Read file FILE_NAME via the GDB `list' function
// Really slow, is guaranteed to work for source files.
String SourceCode::read_from_gdb(const string& file_name, long& length,
                                 bool /* silent */)
{
    length = 0;
    if (!can_do_gdb_command())
        return 0;
    if (gdb->type() == JDB)
        return 0;                // Won't work with JDB

    StatusDelay delay("Reading file " + quote(file_name) +
                      " from " + gdb->title());

    string command;
    switch (gdb->type())
    {
    case BASH:
    case DBX:
    case PYDB:
        command = "list 1," HUGE_LINE_NUMBER;
        break;

    case DBG: // Is this correct? DBG "list" sommand seems not to do anything
    case GDB:
        command = "list " + file_name + ":1," HUGE_LINE_NUMBER;
        break;

    case PERL:
        command = "l 1-" HUGE_LINE_NUMBER;
        break;

    case JDB:
        command = "list " + file_name;
        break;

    case MAKE:  // Don't have a "list" function yet.
        command = "";
        break;

    case XDB:
        command = "w " HUGE_LINE_NUMBER;
        break;
    }
    string listing = gdb_question(command, -1, true);

    // GDB listings have the format <NUMBER>\t<LINE>.
    // Copy LINE only; line numbers will be re-added later.
    // Note that tabs may be expanded to spaces due to a PTY interface.
    String text = XtMalloc(listing.length());

    int i = 0;
    length = 0;
    while (i < int(listing.length()))
    {
        int count = 0;

        // Skip leading spaces.  Some debuggers also issue `*', `=',
        // or `>' to indicate the current position.
        while (count < 8
               && i < int(listing.length())
               && (isspace(listing[i])
                   || listing[i] == '='
                   || listing[i] == '*'
                   || listing[i] == '>'))
            i++, count++;

        if (i < int(listing.length()) && isdigit(listing[i]))
        {
            // Skip line number
            while (i < int(listing.length()) && isdigit(listing[i]))
                i++, count++;

            // Skip `:' (XDB output)
            if (count < 8 && i < int(listing.length()) && listing[i] == ':')
                i++, count++;

            // Break at first non-blank character or after 8 characters
            while (count < 8 && i < int(listing.length()) && listing[i] == ' ')
                i++, count++;

            // Skip tab character
            if (count < 8 && i < int(listing.length()) && listing[i] == '\t')
                i++;

            // Copy line
            while (i < int(listing.length()) && listing[i] != '\n')
                text[length++] = listing[i++];

            // Copy newline character
            text[length++] = '\n';
            i++;
        }
        else
        {
            int start = i;

            // Some other line -- the prompt, maybe?
            while (i < int(listing.length()) && listing[i] != '\n')
                i++;
            if (i < int(listing.length()))
                i++;

            string msg = listing.from(start);
            msg = msg.before('\n');
            if (!msg.contains("end of file")) // XDB issues this
                post_gdb_message(msg, true, source_text_w);
        }
    }

    if (text[0] == 'i' && text[1] == 'n' && text[2] == ' ')
    {
        // GDB 5.0 issues only `LINE_NUMBER in FILE_NAME'.  Treat this
        // like an error message.
        length = 0;
    }

    text[length] = '\0';  // be sure to null-terminate

    if (length == 0)
        delay.outcome = "failed";

    return text;
}

// Read file FILE_NAME and format it
String SourceCode::read_indented(string& file_name, long& length,
                                 SourceOrigin& origin, bool silent)
{
    length = 0;
    Delay delay;
    long t;

    String text = 0;
    origin = ORIGIN_NONE;
    string full_file_name = file_name;

    if (gdb->type() == JDB && !file_name.contains('/'))
    {
        // FILE_NAME is a class name.  Search class in JDB `use' path.
        text = read_class(file_name, full_file_name, origin, length, true);
    }

    if (gdb->type() == PERL && file_name.contains('-', 0))
    {
        // Attempt to load `-e' in Perl or likewise
        origin = ORIGIN_NONE;
        return 0;
    }

    if (text == 0 || length == 0)
    {
        for (int trial = 1; (text == 0 || length == 0) && trial <= 3; trial++)
        {
            switch (trial)
            {
            case 1:
                // Loop #1: use full path of file
                full_file_name = full_path(file_name);
                break;

            case 2:
                // Loop #2: ask debugger for full path, using `edit'
                full_file_name = full_path(dbx_path(file_name));
                if (full_file_name == full_path(file_name))
                    continue;
                break;

            case 3:
                // Loop #3: used file list from debugger
                full_file_name = get_source_name(file_name);
                if (full_file_name == full_path(file_name))
                    continue;
                break;
            }

            // Attempt #1.  Try to read file from remote source.
            if ((text == 0 || length == 0) && remote_gdb())
            {
                text = read_remote(full_file_name, length, true);
                if (text != 0)
                    origin = ORIGIN_REMOTE;
            }

            // Attempt #2.  Read file from local source.
            if ((text == 0 || length == 0) && !remote_gdb())
            {
                text = read_local(full_file_name, length, true);
                if (text != 0)
                    origin = ORIGIN_LOCAL;
            }

            // Attempt #3.  Read file from local source, even if we are remote.
            if ((text == 0 || length == 0) && remote_gdb())
            {
                text = read_local(full_file_name, length, true);
                if (text != 0)
                    origin = ORIGIN_LOCAL;
            }
        }
    }

    // Attempt #4.  Read file from GDB.
    if (text == 0 || length == 0)
    {
        string source_name = get_source_name(file_name);

        text = read_from_gdb(source_name, length, silent);

        if (text != 0 && length != 0)
        {
            // Use the source name as file name
            full_file_name = source_name;
            if (text != 0)
                origin = ORIGIN_GDB;
        }
    }

    if ((text == 0 || length == 0) && !silent)
    {
        // All failed - produce an appropriate error message.
        if (gdb->type() == JDB)
            text = read_class(file_name, full_file_name, origin,
                              length, false);
        else if (!remote_gdb())
            text = read_local(full_file_name, length, false);
        else
            text = read_remote(full_file_name, length, false);
    }

    if (text == 0 || length == 0)
    {
        origin = ORIGIN_NONE;
        return 0;
    }

    // At this point, we have a source text.
    file_name = full_file_name;

#if !HAVE_FREETYPE

    // determine utf-8 encoding
    bool utf8 = true;
    // simple test
    for (t = 0; t < length; t++)
    {
        if (((unsigned char)text[t]) == 0xc0 || ((unsigned char)text[t]) == 0xc1 || ((unsigned char)text[t]) >= 0xf5)
        {
            utf8 = false;
            break;
        }
    }

    // determine new length and check encoding
    if (utf8 == true)
    {
        int newlength = 0;
        int pos = 0;
        wchar_t unicode;
        while (pos<length)
        {
            bool res = utf8toUnicode(unicode, text, pos, length);
            if (res==false)
                break;

            newlength ++;
        }

        if (pos==length)
        {
            // map utf-8 to latin1
            // undisplayable characters (unicode > 255) are mapped to "_"
            // This should be ok for source code, since only the display
            // of non-latin1 comments and string literals is affected.
            char* newtext = XtMalloc(unsigned(newlength + 1));

            int pos = 0;
            wchar_t unicode;
            int newpos = 0;
            while (pos<length)
            {
                bool res = utf8toUnicode(unicode, text, pos, length);
                if (res==false)
                    break;

                if (unicode<=255)
                    newtext[newpos] = unicode;
                else
                    newtext[newpos] = '_';

                newpos++;
            }

            XtFree(text);

            length = newlength;
            text = newtext;
        }
    }
#endif

    // Determine text length and number of lines
    int lines = 0;
    for (t = 0; t < length; t++)
        if (text[t] == '\n')
            lines++;

    int indented_text_length = length;
    if (length > 0 && text[length - 1] != '\n')
    {
        // Text does not end in '\n':
        // Make room for final '\n'
        indented_text_length += 1;

        // Make room for final line
        lines++;
    }

    // Make room for line numbers
    line_indent_amount = 4;
    if (lines>=1000)
        line_indent_amount = 5;
    if (lines>=10000)
        line_indent_amount = 6;

    int indent = calculate_indent();
    indented_text_length += (indent + script_indent_amount) * lines;

    String indented_text = XtMalloc(indented_text_length + 1);

    string line_no_s = replicate(' ', indent);

    t = 0;
    char *pos_ptr = indented_text; // Writing position in indented_text
    while (t < length)
    {
        assert (pos_ptr - indented_text <= indented_text_length);

        // Increase line number
        int i;
        for (i = indent - 2; i >= 0; i--)
        {
            char& c = line_no_s[i];
            if (c == ' ')
            {
                c = '1';
                break;
            }
            else if (c < '9')
            {
                c++;
                break;
            }
            else
                c = '0';
        }

        // Copy line number
        for (i = 0; i < indent; i++)
            *pos_ptr++ = display_line_numbers ? line_no_s[i] : ' ';

        if (indent < script_indent_amount)
        {
            // Check for empty line or line starting with '\t'
            int spaces = 0;
            while (t + spaces < length && text[t + spaces] == ' ')
                spaces++;

            if (spaces < script_indent_amount)
            {
                if (t + spaces >= length ||
                    text[t + spaces] == '\n' ||
                    text[t + spaces] == '\t')
                {
                    // Prepend a few space characters
                    while (spaces < script_indent_amount)
                    {
                        *pos_ptr++ = ' ';
                        spaces++;
                    }
                }
            }
        }

        // Copy remainder of line
        while (t < length && text[t] != '\n')
            *pos_ptr++ = text[t++];

        // Copy '\n' or '\0'
        if (t == length)
        {
            // Text doesn't end in '\n'
            *pos_ptr++ = '\n';
        }
        else
        {
            *pos_ptr++ = text[t++];
        }
    }
    *pos_ptr = '\0';

    XtFree(text);

    length = pos_ptr - indented_text;
    return indented_text;
}

// Read file FILE_NAME into current_source; get it from the cache if possible
int SourceCode::read_current(string& file_name, bool force_reload, bool silent, Widget w)
{
    source_text_w = w; // store widget for error message output
    string requested_file_name = file_name;

    if (cache_source_files && !force_reload && filecache.find(file_name)!=filecache.end())
    {
        const FileCacheEntry &cached = filecache[file_name];
        current_source = cached.text;
        current_origin = cached.origin;
        file_name      = cached.file_name;

        if (gdb->type() == JDB)
        {
            // In JDB, a single source may contain multiple classes.
            // Store current class name FILE_NAME as source name.
            source_name_cache[file_name] = requested_file_name;
        }
    }
    else
    {
        long length = 0;
        SourceOrigin orig;
        String indented_text = read_indented(file_name, length, orig, silent);
        if (indented_text == 0 || length == 0)
            return -1;                // Failure

        current_source = string(indented_text, length);
        current_origin = orig;
        XtFree(indented_text);

        if (current_source.length() > 0)
        {
            FileCacheEntry newentry;
            newentry.text = current_source;
            newentry.origin = current_origin;
            newentry.file_name = file_name;

            filecache[file_name] = newentry;

            if (file_name != requested_file_name)
                filecache[requested_file_name] = newentry;
        }

        int null_count = current_source.freq('\0');
        if (null_count > 0 && !silent)
            post_warning(file_name + ": binary file",
                         "source_binary_warning", source_text_w);
    }

    // Untabify current source, using the current tab width
    untabify(current_source, tab_width, calculate_indent());

    // Setup global parameters

    // Number of lines
    line_count   = current_source.freq('\n');
    textpos_of_line.clear();
    textpos_of_line.reserve(line_count + 2);
    textpos_of_line.push_back((XmTextPosition(0)));
    bytepos_of_line.clear();
    bytepos_of_line.reserve(line_count + 2);
    bytepos_of_line.push_back((XmTextPosition(0)));
#if !HAVE_FREETYPE
    char_count = current_source.length();
    for (int i = 0; i < int(current_source.length()); i++)
    {
        if (current_source[i] == '\n')
        {
            textpos_of_line.push_back((XmTextPosition(i + 1)));
            bytepos_of_line.push_back(i + 1);
        }
    }
#else
    int length = int(current_source.length());
    char_count = 0;
    int bytepos = 0;
    wchar_t unicode;
    while (bytepos<length)
    {
        bool res = utf8toUnicode(unicode, current_source.chars(), bytepos, length);
        if (res==false)
            break;

        char_count ++;
        if (unicode == '\n')
        {
            textpos_of_line.push_back((XmTextPosition(char_count)));
            bytepos_of_line.push_back(bytepos);
        }
    }

#endif
    assert(int( textpos_of_line.size()) == line_count + 1);

    if (current_source.length() == 0)
        return -1;

    // Set current file name
    current_file_name = file_name;

    return 0;
}

/*! Get the character position of the start of \c line
 * \param[in] line line number with range: 1..number of lines
 * \return return the position
 */
XmTextPosition SourceCode::pos_of_line(int line)
{
    line --; // external counting starts with 1
    if (line < 0 || line > line_count || line >= int( textpos_of_line.size()))
        return 0;

    return textpos_of_line[line];
}

/*! Get line number from character position
 * \param[in] pos character position
 * \return returns the line number with range: 1..number of lines
 */
int SourceCode::line_of_pos(XmTextPosition pos)
{
    if (textpos_of_line.size()==0)
        return 0;

    auto it = std::lower_bound(textpos_of_line.begin(), textpos_of_line.end(), pos+1);
    if (it != textpos_of_line.begin())
        return std::distance(textpos_of_line.begin(), it);

    return textpos_of_line.back();
}

/*! Get line number from byte position
 * \param[in] pos character position
 * \return returns the line number with range: 1..number of lines
 */
int SourceCode::line_of_bytepos(int pos)
{
    if (bytepos_of_line.size()==0)
        return 0;

    auto it = std::lower_bound(bytepos_of_line.begin(), bytepos_of_line.end(), pos+1);
    if (it != bytepos_of_line.begin())
        return std::distance(bytepos_of_line.begin(), it);

    return bytepos_of_line.back();
}

/*! Get position of start of line from character position
 * \param[in] pos character position
 * \return returns the position of the start of the line
 */
XmTextPosition SourceCode::startofline_at_pos(XmTextPosition pos)
{
    if (textpos_of_line.size()==0)
        return 0;

    auto it = std::lower_bound(textpos_of_line.begin(), textpos_of_line.end(), pos+1);

    if (it == textpos_of_line.begin())
        return 0;

    --it;
    if (it != textpos_of_line.begin())
        return *it;

    return textpos_of_line.back();
}

/*! Determine if character at \c pos is the last character of the line
 * \param[in] pos character position
 * \return returns true for the last character
 */
XmTextPosition SourceCode::endofline_at_pos(XmTextPosition pos)
{
    if (textpos_of_line.size()==0)
        return 0;

    auto it = std::lower_bound(textpos_of_line.begin(), textpos_of_line.end(), pos+1);
    if (it != textpos_of_line.begin())
        return *it - 1;

    return 0;
}

const subString SourceCode::get_source_line(int line)
{
    if (line<1 || line > int(bytepos_of_line.size()))
        return current_source.at(0, 0); // empty substring

    int start = bytepos_of_line[line-1];

    int stop = current_source.length();
    if (line < int(bytepos_of_line.size()))
        stop = bytepos_of_line[line];

    return current_source.at(start, stop - start - 1);
}

string SourceCode::get_source_lineASCII(int line)
{
    if (line<1 || line > int(bytepos_of_line.size()))
        return string(""); // empty string

    int pos = bytepos_of_line[line-1];
    string linestr;
    while (pos<int(current_source.length()))
    {
        wchar_t unicode;
        bool res = utf8toUnicode(unicode, current_source.chars(), pos, current_source.length());
        if (res==false)
            break;

        if (unicode<=127)
            linestr += char(unicode);
        else
            linestr += '_';

        if (unicode == '\n')
            break;
    }

    return linestr;
}

const subString SourceCode::get_source_at(int pos, int length)
{
    if (length <= 0)
        return current_source.at(0, 0); // empty substring

    int startline = line_of_pos(pos) -1;
    int charpos = textpos_of_line[startline];
    int bytepos = bytepos_of_line[startline];
    int bytestart = bytepos;

    while (bytepos<int(current_source.length()) && charpos<pos+length)
    {
        wchar_t unicode;
        bool res = utf8toUnicode(unicode, current_source.chars(), bytepos, current_source.length());
        if (res==false)
            break;
        charpos++;

        if (charpos==pos)
            bytestart = bytepos;
    }
    int byteend = bytepos;
    return current_source.at(bytestart, byteend-bytestart);
}

int SourceCode::charpos_to_bytepos(XmTextPosition pos)
{
    int startline = line_of_pos(pos) - 1;
    XmTextPosition charpos = textpos_of_line[startline];
    int bytepos = bytepos_of_line[startline];
    while (bytepos<int(current_source.length()))
    {
        wchar_t unicode;
        bool res = utf8toUnicode(unicode, current_source.chars(), bytepos, current_source.length());
        if (res==false)
            break;
        charpos++;

        if (charpos==pos)
            return bytepos;
    }

    return 0;
}

XmTextPosition SourceCode::bytepos_to_charpos(int pos)
{
    int startline = line_of_bytepos(pos) - 1;
    XmTextPosition charpos = textpos_of_line[startline];
    int bytepos = bytepos_of_line[startline];
    while (bytepos<int(current_source.length()))
    {
        wchar_t unicode;
        bool res = utf8toUnicode(unicode, current_source.chars(), bytepos, current_source.length());
        if (res==false)
            break;
        charpos++;

        if (bytepos==pos)
            return charpos;
    }

    return 0;
}



// Clear the file cache
void SourceCode::clear_file_cache()
{
    source_name_cache.clear();
    filecache.clear();
    bad_files.clear();
}

static const int MAX_TAB_WIDTH = 256;

//Change tab width
bool SourceCode::set_tab_width(int width)
{
    if (width <= 0)
        return false;

    if (tab_width == width)
        return false;

    // Make sure the tab width stays within reasonable ranges
    tab_width = min(max(width, 1), MAX_TAB_WIDTH);

    return !current_file_name.empty();
}

//Change indentation
bool SourceCode::set_indent(int source_indent, int script_indent)
{
    if (source_indent < 0 || script_indent < 0)
        return false;

    if (source_indent == source_indent_amount && script_indent == script_indent_amount)
        return false;

    source_indent_amount = min(max(source_indent, 0), MAX_INDENT);
    script_indent_amount = min(max(script_indent, 0), MAX_INDENT);

    return !current_file_name.empty();
}

// Change setting of display_line_numbers
bool SourceCode::set_display_line_numbers(bool set)
{
    if (display_line_numbers == set)
        return false;

    display_line_numbers = set;
    return true;
}




//-----------------------------------------------------------------------
// Return source name
// use "" as parameter filename the current_file_name is used
//-----------------------------------------------------------------------

string SourceCode::get_source_name(string filename)
{
    if (filename =="")
        filename = current_file_name;

    string source = "";

    switch (gdb->type())
    {
    case GDB:
        // GDB internally recognizes only `source names', i.e., the
        // source file name as compiled into the executable.
        if (source_name_cache[filename].empty())
        {
            // Try the current source.
            string ans = gdb_question("info source");
            if (ans != NO_GDB_ANSWER)
            {
                ans = ans.before('\n');
                ans = ans.after(' ', -1);

                if (base_matches(ans, filename))
                {
                    // For security, we request that source and current
                    // file have the same basename.
                    source_name_cache[filename] = ans;
                }
                else
                {
                    // The current source does not match the current file.
                    // Try all sources.
                    static const string all_sources = "<ALL SOURCES>";

                    if (source_name_cache[all_sources].empty())
                    {
                        std::vector<string> sources;
                        get_gdb_sources(sources);

                        if (sources.size() > 0)
                        {
                            ans = "";
                            for (int i = 0; i < int(sources.size()); i++)
                                ans += sources[i] + '\n';

                            source_name_cache[all_sources] = ans;
                        }
                    }

                    ans = source_name_cache[all_sources];
                    if (!ans.empty())
                    {
                        int n = ans.freq('\n');
                        string *sources = new string[n + 1];
                        split(ans, sources, n + 1, '\n');

                        for (int i = 0; i < n + 1; i++)
                        {
                            if (base_matches(sources[i], filename))
                            {
                                const string& src = sources[i];
                                source_name_cache[filename] = src;
                                break;
                            }
                        }

                        delete[] sources;

                        if (source_name_cache[filename].empty())
                        {
                            // No such source text.  Store the base name
                            // such that GDB is not asked again.
                            string base = basename(filename.chars());
                            source_name_cache[filename] = base;
                        }
                    }
                }
            }
        }

        source = source_name_cache[filename];
        break;

    case BASH:
    case DBG:
    case DBX:
    case MAKE:
    case PERL:
    case PYDB:
    case XDB:
        if (app_data.use_source_path)
        {
            // These debuggers use full file names.
            source = full_path(filename);
        }
        break;

    case JDB:
        if (source_name_cache.find(filename)!=source_name_cache.end())
        {
            // Use the source name as stored by read_class()
            source = source_name_cache[filename];
        }
        if (source.empty())
        {
            source = basename(filename.chars());
            strip_java_suffix(source);
        }
        break;
    }

    // In case this does not work, use the current base name.
    if (source.empty())
        source = basename(filename.chars());

    return source;
}

string SourceCode::current_source_name()
{
    return get_source_name("");
}


