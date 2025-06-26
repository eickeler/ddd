// GDBAgent derived class to support GDB debugger
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
#include "GDBAgent_GDB.h"
#include "regexps.h"
#include "string-fun.h"
#include "BreakPoint.h"

// Note:  These target debugger configuration variables are defined 
// here rather than in the class because they are accessed even when
// they are not in the current target debugger instance, for example, 
// to set or save init_commands or settings for BASH or DBX during 
// startup/shutdown.  There can be only a single GDBAgent instance
// at any time.  

char *GDBAgent_GDB_init_commands;
char *GDBAgent_GDB_settings;

static bool ends_in(const string& answer, const char *prompt)
{
    return answer.contains(prompt, answer.length() - strlen(prompt));
}

GDBAgent_GDB::GDBAgent_GDB (XtAppContext app_context,
	      const string& gdb_call):
    GDBAgent (app_context, gdb_call, GDB)
{
    if (path().contains("wdb"))
        _title = "WDB";
    else
        _title = "GDB";
    
    _has_watch_command = WATCH_CHANGE | WATCH_READ | WATCH_WRITE;
    _has_info_multiple_breakpoint = true;

}

// Return true iff ANSWER ends with primary prompt.
bool GDBAgent_GDB::ends_with_prompt (const string& ans)
{
    string answer = ans;
    strip_control(answer);

    // GDB reads in breakpoint commands using a `>' prompt
    if (recording() && answer.contains('>', -1))
    {
        last_prompt = ">";
        return true;
    }

    // In annotation level 1, GDB `annotates' its prompt.
    if (answer.contains("\032\032prompt\n", -1))
        return true;

    // DUPLICATED FROM GDBAgent_DBX::ends_with_prompt()
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
bool GDBAgent_GDB::ends_with_secondary_prompt (const string& ans) const
{
    string answer = ans;
    strip_control(answer);

    // Prompt is `> ' at beginning of line
    return answer == "> " || ends_in(answer, "\n> ");
}

// Remove GDB prompt
void GDBAgent_GDB::cut_off_prompt(string& answer) const
{
    if (recording() && answer.contains('>', -1))
    {
        answer = answer.before('>', -1);
	return;
    }

    answer = answer.before('(', -1);
}

string GDBAgent_GDB::print_command(const char *expr, bool internal) const
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

string GDBAgent_GDB::history_file() const
{
    const char *g = getenv("GDBHISTFILE");
    if (g != 0)
        return g;
    else
        return "./.gdb_history";
}

string GDBAgent_GDB::make_command(const string& args) const
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

string GDBAgent_GDB::regs_command(bool all) const
{
    if (all)
	return "info all-registers";
    else
	return "info registers";
}

string GDBAgent_GDB::watch_command(const string& expr, WatchMode w) const
{
    if ((has_watch_command() & w) != w)
	return "";
    if ((w & WATCH_CHANGE) == WATCH_CHANGE)
	return "watch " + expr;
    if ((w & WATCH_ACCESS) == WATCH_ACCESS)
	return "awatch " + expr;
    if ((w & WATCH_READ) == WATCH_READ)
	return "rwatch " + expr;
    return "";
}

string GDBAgent_GDB::enable_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "enable" + bp;
}

string GDBAgent_GDB::disable_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "disable" + bp;
}

string GDBAgent_GDB::delete_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "delete" + bp;
}

string GDBAgent_GDB::ignore_command(const string& bp, int count) const
{
    return "ignore " + bp + " " + itostring(count);
}

string GDBAgent_GDB::debug_command(const char *program, string args) const
{
    if (!args.empty() && !args.contains(' ', 0))
	args.prepend(' ');

    if (is_windriver_gdb())
	return "load " + quote_file(program);
    else
	return "file " + quote_file(program);
}

string GDBAgent_GDB::signal_command(int sig) const
{
    string n = itostring(sig);

    return "signal " + n;
}

string GDBAgent_GDB::run_command(string args) const
{
    if (!args.empty() && !args.contains(' ', 0))
	args = " " + args;

    string c;
    if (args.empty())
	c = "set args\n";
    return c + "run" + args;
}

string GDBAgent_GDB::attach_command(int pid, const string& file) const
{
    /* UNUSED */ (void (file));
    return "attach " + itostring(pid);
}

string GDBAgent_GDB::assign_command(const string& var, const string& expr) const
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
void GDBAgent_GDB::parse_break_info (BreakPoint *bp, string &info) 
{
    // Actual parsing code is in BreakPoint
    bp->process_gdb (info);
}

// Command to restore breakpoint
// Return commands to restore this breakpoint, using the dummy number
// NR.  If AS_DUMMY is set, delete the breakpoint immediately in order
// to increase the breakpoint number.  If ADDR is set, use ADDR as
// (fake) address.  If COND is set, use COND as (fake) condition.
// Return true iff successful.
void GDBAgent_GDB::restore_breakpoint_command (std::ostream& os, 
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
