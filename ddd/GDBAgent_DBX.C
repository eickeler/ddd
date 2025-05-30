// GDBAgent derived class to support DBX debugger
//
// Copyright (c) 2023-2025  Free Software Foundation, Inc.
// Written by Michael J. Eager <eager@gnu.org>
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

#include "GDBAgent.h"
#include "GDBAgent_DBX.h"
#include "regexps.h"
#include "base/cook.h"
#include "string-fun.h"
#include "index.h"

char *GDBAgent_DBX_init_commands;
char *GDBAgent_DBX_settings;

static bool ends_in(const string& answer, const char *prompt)
{
    return answer.contains(prompt, answer.length() - strlen(prompt));
}

GDBAgent_DBX::GDBAgent_DBX (XtAppContext app_context,
	      const string& gdb_call):
    GDBAgent (app_context, gdb_call, DBX)
{
    if (is_ladebug())
        _title = "Ladebug";
    else
        _title = "DBX";
    _has_frame_command = false;
    _has_func_command = true;
    _has_file_command = true;
    _has_setenv_command = true;
    _has_edit_command = true;
    _has_regs_command = false;
    _has_when_command = true;
    _has_when_semicolon = true;
    _has_rerun_command = true;
    _has_watch_command = WATCH_CHANGE;
}

bool GDBAgent_DBX::is_ladebug() const
{
    return (path().contains("ladebug") || prompt().contains("ladebug"));
}

// Return true iff ANSWER ends with primary prompt.
bool GDBAgent_DBX::ends_with_prompt (const string& ans)
{
    string answer = ans;
    strip_control(answer);

    // Any line ending in `(gdb) ' or `(dbx) ' is a prompt.
    int i = answer.length() - 1;
    if (i < 0 || answer[i] != ' ')
        return false;

    while (i >= 0 && answer[i] != '\n' && answer[i] != '(')
        i--;
    if (i < 0 || answer[i] != '(')
        return false;

    string possible_prompt = answer.from(i);
#if RUNTIME_REGEX
    // Marc Lepage <mlepage@kingston.hummingbird.com> says that
    // DBX on Solaris 2.5 has a prompt like `(dbx N) '.  We're
    // liberal here and allow anything in the form `(NAME) ',
    // where the first word in NAME must contain a `db' or `deb'.
    // (`deb' is there to support DEC's `ladebug')
    static regex rxprompt("[(][^ )]*de?b[^)]*[)] ");
#endif
    if (possible_prompt.matches(rxprompt))
    {
        last_prompt = possible_prompt;
        recording(false);
        return true;
    }
    return false;
}

// Return true iff ANSWER ends with secondary prompt.
bool GDBAgent_DBX::ends_with_secondary_prompt (const string& ans) const
{
    string answer = ans;
    strip_control(answer);

    if (ends_in(answer, "]: "))
    {
        // AIX DBX issues `Select one of [FROM - TO]: ' in the last line
        // Reported by Jonathan Edwards <edwards@intranet.com>
#if RUNTIME_REGEX
        static regex rxselect("Select one of \\[[0-9]+ - [0-9]+\\]: ");
#endif
        int idx = index(answer, rxselect, "Select one of ", -1);
        if (idx >= 0 && answer.index('\n', idx) < 0)
    	    return true;
    }
    if (ends_in(answer, "): "))
    {
        // DEC DBX wants a file name when being invoked without one:
        // `enter object file name (default is `a.out'): '
        // Reported by Matthew Johnson <matthew.johnson@speechworks.com>
#if RUNTIME_REGEX
        static regex rxenter_file_name("enter .*file name");
#endif

        int idx = index(answer, rxenter_file_name, "enter ", -1);
        if (idx >= 0 && answer.index('\n', idx) < 0)
    	    return true;
    }

    // Prompt is `> ' at beginning of line
    return answer == "> " || ends_in(answer, "\n> ");
}

// Remove DBX prompt
void GDBAgent_DBX::cut_off_prompt(string& answer) const
{
    answer = answer.before('(', -1);
}

// DBX 3.0 wants `print -r' instead of `print' for C++
string GDBAgent_DBX::print_command(const char *expr, bool internal) const
{
    string cmd;

    if (internal && has_output_command())
	cmd = "output";
    else
	cmd = "print";

    if (has_print_r_option())
	cmd += " -r";

    if (strlen(expr) != 0) {
	cmd += ' ';
	cmd += expr;
    }

    return cmd;
}

string GDBAgent_DBX::info_locals_command() const { return "dump"; }

string GDBAgent_DBX::make_command(const string& args) const
{
    string cmd;

    if (has_make_command())
	cmd = "make";
    else
	cmd = "sh make";
 
   if (args.empty())
	return cmd;
    else
	return cmd + " " + args;
}

string GDBAgent_DBX::regs_command(bool all) const
{
    if (all)
	return "regs -F";
    else
	return "regs";
}

string GDBAgent_DBX::watch_command(const string& expr, WatchMode w) const
{
    if ((has_watch_command() & w) != w)
	return "";

    if ((w & WATCH_CHANGE) == WATCH_CHANGE)
    {
        if (has_handler_command())
        {
    	    // Solaris 2.6 DBX wants `stop change VARIABLE'
    	    return "stop change " + expr;
        }
        else
        {
	    // `Traditional' DBX notation
	    return "stop " + expr;
        }
    }
    return "";
}

string GDBAgent_DBX::echo_command(const string& text) const 
{
  return print_command(quote(text), false);
}

string GDBAgent_DBX::whatis_command(const string& text) const
{
    if (has_print_r_option())
	return "whatis -r " + text;
    else
	return "whatis " + text;
}

string GDBAgent_DBX::enable_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    if (is_ladebug())
	return "enable" + bp;
    else if (has_handler_command())
	return "handler -enable" + bp;
    else
	return "";
}

string GDBAgent_DBX::disable_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    if (is_ladebug())
	return "disable" + bp;
    else if (has_handler_command())
	return "handler -disable" + bp;
    else
	return "";
}

string GDBAgent_DBX::delete_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "delete" + bp;
}

string GDBAgent_DBX::ignore_command(const string& bp, int count) const
{
    if (has_handler_command())
	return "handler -count " + bp + " " + itostring(count);
    else
	return "";
}

string GDBAgent_DBX::debug_command(const char *program, string args) const
{
    if (!args.empty() && !args.contains(' ', 0))
	args.prepend(' ');

    if (is_ladebug())
	return string("load ") + program;       // Compaq Ladebug
    else if (has_givenfile_command())
	return string("givenfile ") + program; // SGI DBX
    else
	return string("debug ") + program;     // SUN DBX
}

string GDBAgent_DBX::signal_command(int sig) const
{
    string n = itostring(sig);

    if (has_cont_sig_command())
	return "cont sig " + n; // SUN DBX
    else
	return "cont " + n;     // Other DBXes
}

string GDBAgent_DBX::run_command(string args) const
{
    if (!args.empty() && !args.contains(' ', 0))
	args = " " + args;

    if (args.empty() && has_rerun_command() && rerun_clears_args())
	return "rerun";
    else
	return "run" + args;
}

string GDBAgent_DBX::rerun_command() const
{
	if (has_rerun_command() && !rerun_clears_args())
	    return "rerun";
	else
	    return "run";
}

string GDBAgent_DBX::attach_command(int pid, const string& file) const
{
    if (has_handler_command())
	return "debug - " + itostring(pid);	           // Sun DBX
    if (has_addproc_command())
	return "addproc " + itostring(pid);	           // SGI DBX
    else if (is_ladebug() && has_attach_command())
	return string("set $stoponattach=1\n") +
	    "attach " + itostring(pid) + " " + file;   // DEC ladebug
    else if (has_attach_command())
	return "attach " + itostring(pid);             // Others
    else
	return "debug " + file + " " + itostring(pid); // Others
}

string GDBAgent_DBX::detach_command(int pid) const
{
    if (has_addproc_command())
	return "delproc " + itostring(pid);	// SGI DBX
    else
	return "detach";	// Others
}

string GDBAgent_DBX::assign_command(const string& var, const string& expr) const
{
    string cmd = "assign";

    cmd += " " + var + " ";

    switch (program_language())
    {
    case LANGUAGE_BASH:
    case LANGUAGE_C:
    case LANGUAGE_FORTRAN:
    case LANGUAGE_JAVA:
    case LANGUAGE_MAKE:
    case LANGUAGE_PERL:
    case LANGUAGE_PHP:
    case LANGUAGE_PYTHON:	// FIXME: vrbl names can conflict with commands
    case LANGUAGE_OTHER:
	cmd += "=";
	break;

    case LANGUAGE_ADA:
    case LANGUAGE_PASCAL:
    case LANGUAGE_CHILL:
	cmd += ":=";
	break;
    }

    return cmd + " " + expr;
}

// Some DBXes issue the local variables via a frame line, just like
// `set_date(d = 0x10003060, day_of_week = Sat, day = 24, month = 12,
// year = 1994) LOCATION', where LOCATION is either `[FRAME]' (DEC
// DBX) or `, line N in FILE' (AIX DBX).  Make this more readable.
void GDBAgent_DBX::clean_frame_line(string &value) 
{
    string initial_line = value.before('\n');
    strip_trailing_space(initial_line);

#if RUNTIME_REGEX
    static regex rxdbxframe("[a-zA-Z_$][a-zA-Z_$0-9]*[(].*[)].*"
			    "([[].*[]]|, line .*)");
#endif
    if (initial_line.matches(rxdbxframe))
    {
        // Strip enclosing parentheses
        initial_line = initial_line.after('(');
        int index = initial_line.index(')', -1);
        initial_line = initial_line.before(index);

        // Place one arg per line
        initial_line.gsub(", ", "\n");
       
        value = initial_line + value.from('\n');
    }
}

