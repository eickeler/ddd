// GDBAgent derived class to support MAKE debugger
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
#include "GDBAgent_MAKE.h"
#include "regexps.h"
#include "base/cook.h"
#include "BreakPoint.h"

char *GDBAgent_MAKE_init_commands;
char *GDBAgent_MAKE_settings;

GDBAgent_MAKE::GDBAgent_MAKE (XtAppContext app_context,
	      const string& gdb_call):
    GDBAgent (app_context, gdb_call, MAKE)
{
    _has_display_command = false;
    _has_clear_command = false;
    _has_jump_command = false;
    _has_regs_command = false;
    _has_named_values = false;
    _has_err_redirection = false;
    _has_examine_command = false;
    _has_attach_command = false;
    _program_language = LANGUAGE_MAKE;
}

// Return true iff ANSWER ends with primary prompt.
bool GDBAgent_MAKE::ends_with_prompt (const string& ans)
{
    string answer = ans;
    strip_control(answer);

    // Any line ending in `remake<...> ' is a prompt.
    // Since N does not make sense in DDD, we use `DB<> ' instead.

#if RUNTIME_REGEX
    static regex rxmakeprompt("remake<+[(]*[.0-9][)]*>+[.]*");
#endif

    int i = answer.length() - 1;
    if (i < 1 || answer[i] != ' ' || (answer[i - 1] != '>' && answer[i - 1] != '.'))
        return false;

    while (i >= 0 && answer[i] != '\n' ) {
      if (answer.contains("remake<", i)) {
        string possible_prompt = answer.from(i);
        if (possible_prompt.matches(rxmakeprompt)) {
          last_prompt = possible_prompt;
          return true;
        }
      }
      i--;
    }
    return false;
}

// Remove prompt
void GDBAgent_MAKE::cut_off_prompt(string& answer) const
{
    // Check for prompt at the end of the last line
    if (answer.contains(last_prompt, -1))
    {
        answer = answer.before(int(answer.length()) - 
    			       int(last_prompt.length()));
    }
}

string GDBAgent_MAKE::print_command(const char *expr, bool internal) const
{
    /* UNUSED */ (void (internal)); 
    string cmd = "x";

    if (strlen(expr) != 0) {
	cmd += ' ';
	cmd += expr;
    }

    return cmd;
}

string GDBAgent_MAKE::pwd_command() const { return "shell pwd"; }

string GDBAgent_MAKE::make_command(const string& args) const
{
    string cmd = "shell make";

    if (args.empty())
	return cmd;
    else
	return cmd + " " + args;
}

string GDBAgent_MAKE::echo_command(const string& text) const 
{
  return "examine " + quote(text);
}

string GDBAgent_MAKE::debug_command(const char *program, string args) const
{
    if (!args.empty() && !args.contains(' ', 0))
	args.prepend(' ');

    return string("run ") + program + args;
}

string GDBAgent_MAKE::assign_command(const string& var, const string& expr) const
{
    string cmd = "set variable";

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
void GDBAgent_MAKE::parse_break_info (BreakPoint *bp, string &info) 
{
    // Actual parsing code is in BreakPoint
    // Handle this like GDB
    bp->process_gdb (info);
}
