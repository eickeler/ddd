// GDBAgent derived class to support PYDB debugger
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
#include "GDBAgent_PYDB.h"
#include "base/cook.h"
#include "regexps.h"
#include "string-fun.h"
#include "BreakPoint.h"

char *GDBAgent_PYDB_init_commands;
char *GDBAgent_PYDB_settings;

GDBAgent_PYDB::GDBAgent_PYDB (XtAppContext app_context,
	      const string& gdb_call):
    GDBAgent (app_context, gdb_call, PYDB)
{
    _title = "PYDB";
    _has_clear_command = false;
    _has_regs_command = false;
    _has_named_values = false;
    _has_err_redirection = false;
    _has_examine_command = false;
    _has_attach_command = false;
    _program_language = LANGUAGE_PYTHON;
}

// Return true iff ANSWER ends with primary prompt.
bool GDBAgent_PYDB::ends_with_prompt (const string& ans)
{
    string answer = ans;
    strip_control(answer);

    // Any line ending in `(Pydb) ' is a prompt.

#if RUNTIME_REGEX
    static regex rxpyprompt("[(]+Pydb[)]+");
#endif

    int i = answer.length() - 1;
    if (i < 1 || answer[i] != ' ' || answer[i - 1] != ')')
        return false;

    while (i >= 0 && answer[i] != '\n' ) {
      if (answer.contains("(Pydb)", i)) {
        string possible_prompt = answer.from(i);
        if (possible_prompt.matches(rxpyprompt)) {
          last_prompt = possible_prompt;
          return true;
        }
      }
      i--;
    }
    return false;
}

// Remove prompt
void GDBAgent_PYDB::cut_off_prompt(string& answer) const
{
    // Check for prompt at the end of the last line
    if (answer.contains(last_prompt, -1))
    {
        answer = answer.before(int(answer.length()) - 
    			       int(last_prompt.length()));
    }
}

string GDBAgent_PYDB::print_command(const char *expr, bool internal) const
{
    /* UNUSED */ (void (internal)); 
    string cmd = "print";

    if (strlen(expr) != 0) {
	cmd += ' ';
	cmd += expr;
    }

    return cmd;
}

string GDBAgent_PYDB::make_command(const string& args) const
{
    string cmd = "shell make";

    if (args.empty())
	return cmd;
    else
	return cmd + " " + args;
}

string GDBAgent_PYDB::echo_command(const string& text) const 
{
  return "print " + quote(text);
}

string GDBAgent_PYDB::whatis_command(const string& text) const
{
    if (has_print_r_option())
	return "whatis -r " + text;
    else
	return "whatis " + text;
}

string GDBAgent_PYDB::enable_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "enable" + bp;
}

string GDBAgent_PYDB::disable_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "disable" + bp;
}

string GDBAgent_PYDB::delete_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "delete" + bp;
}

string GDBAgent_PYDB::ignore_command(const string& bp, int count) const
{
    return "ignore " + bp + " " + itostring(count);
}

string GDBAgent_PYDB::debug_command(const char *program, string args) const
{
    if (!args.empty() && !args.contains(' ', 0))
	args.prepend(' ');

    return string("debug ") + program + args;
}

string GDBAgent_PYDB::assign_command(const string& var, const string& expr) const
{
    string cmd = "";

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

// Parse breakpoint info response
void GDBAgent_PYDB::parse_break_info (BreakPoint *bp, string &info) 
{
    // Actual parsing code is in BreakPoint
    bp->process_pydb (info);
}
