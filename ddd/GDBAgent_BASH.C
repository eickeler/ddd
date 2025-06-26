// GDBAgent derived class to support BASH debugger
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
#include "GDBAgent_BASH.h"
#include "regexps.h"
#include "base/cook.h"
#include "BreakPoint.h"

char *GDBAgent_BASH_init_commands;
char *GDBAgent_BASH_settings;

GDBAgent_BASH::GDBAgent_BASH (XtAppContext app_context,
	      const string& gdb_call):
    GDBAgent (app_context, gdb_call, BASH)
{
    _title = "Bash";
    _has_jump_command = false;
    _has_regs_command = false;
    _has_named_values = false;
    _has_err_redirection = false;
    _has_examine_command = false;
    _has_attach_command = false;
    _break_info_has_address = false;
    _break_info_has_function = false;
    _program_language = LANGUAGE_BASH;
}

// Return true iff ANSWER ends with primary prompt.
bool GDBAgent_BASH::ends_with_prompt (const string& ans)
{
    string answer = ans;
    strip_control(answer);

    // Any line ending in `bashdb<...> ' is a prompt.
    // Since N does not make sense in DDD, we use `DB<> ' instead.

#if RUNTIME_REGEX
    static regex rxbashprompt("bashdb<+[(]*[0-9][)]*>+");
#endif

    int i = answer.length() - 1;
    if (i < 1 || answer[i] != ' ' || answer[i - 1] != '>')
        return false;

    while (i >= 0 && answer[i] != '\n' ) {
      if (answer.contains("bashdb<", i)) {
        string possible_prompt = answer.from(i);
        if (possible_prompt.matches(rxbashprompt)) {
          last_prompt = possible_prompt;
          return true;
        }
      }
      i--;
    }
    return false;
}

// Remove prompt
void GDBAgent_BASH::cut_off_prompt(string& answer) const
{
    // Check for prompt at the end of the last line
    if (answer.contains(last_prompt, -1))
    {
        answer = answer.before(int(answer.length()) - 
    			       int(last_prompt.length()));
    }
}

string GDBAgent_BASH::print_command(const char *expr, bool internal) const
{
    /* UNUSED */ (void (internal)); 
    string cmd = "x";

    if (strlen(expr) != 0) {
	cmd += ' ';
	cmd += expr;
    }

    return cmd;
}

string GDBAgent_BASH::info_locals_command() const { return "V"; }

string GDBAgent_BASH::pwd_command() const { return "!! pwd"; }

string GDBAgent_BASH::make_command(const string& args) const
{
    string cmd = "shell make";

    if (args.empty())
	return cmd;
    else
	return cmd + " " + args;
}

string GDBAgent_BASH::watch_command(const string& expr, WatchMode w) const
{
    if ((has_watch_command() & w) != w)
	return "";

    if ((w & WATCH_CHANGE) == WATCH_CHANGE)
	return "watch " + expr;
    return "";
}

string GDBAgent_BASH::echo_command(const string& text) const 
{
  return "print " + quote(text);
}

string GDBAgent_BASH::enable_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "enable" + bp;
}

string GDBAgent_BASH::disable_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "disable" + bp;
}

string GDBAgent_BASH::delete_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "delete" + bp;
}

string GDBAgent_BASH::debug_command(const char *program, string args) const
{
    if (!args.empty() && !args.contains(' ', 0))
	args.prepend(' ');

    return string("debug ") + program + args;
}

string GDBAgent_BASH::assign_command(const string& var, const string& expr) const
{
    string cmd = "eval";

    if (!var.empty() && ! ('$' == var[0]))
	return "";		// Cannot set this

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
void GDBAgent_BASH::parse_break_info (BreakPoint *bp, string &info) 
{
    // Actual parsing code is in BreakPoint
    // Handle this like GDB
    bp->process_gdb (info);
}

// Same as GDBAgent_GDB::restore_breakpoint_command()
void GDBAgent_BASH::restore_breakpoint_command (std::ostream& os, 
                        BreakPoint *bp, string pos, string num,
                        string cond, bool as_dummy)
{
    switch (bp->type())
    {
    case BREAKPOINT:
    {
        switch (bp->dispo())
        {
        case BPKEEP:
	case BPDIS:
	    os << "break " << pos << "\n";
	    break;

	case BPDEL:
	    os << "tbreak " << pos << "\n";
	    break;
	}
        break;
    }

    case WATCHPOINT:
    {
        os << watch_command(bp->expr(), bp->watch_mode()) << "\n";
        break;
    }

    case TRACEPOINT:
    case ACTIONPOINT:
    {
        // Not handled - FIXME
        break;
    }
    }

    if (!as_dummy)
    {
        // Extra infos
	if (!bp->enabled() && has_disable_command())
	    os << disable_command(num) << "\n";
	int ignore = bp->ignore_count();
	if (ignore > 0 && has_ignore_command())
	    os << ignore_command(num, ignore) << "\n";
	if (!cond.empty() && has_condition_command())
	    os << condition_command(num, cond.chars()) << "\n";
	if (bp->commands().size() != 0)
	{
	    os << "commands " << num << "\n";
	    for (int i = 0; i < int(bp->commands().size()); i++)
	        os << bp->commands()[i] << "\n";
	    os << "end\n";
	}
    }
}
