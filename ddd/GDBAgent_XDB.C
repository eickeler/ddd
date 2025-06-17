// GDBAgent derived class to support XDB debugger
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
#include "GDBAgent_XDB.h"
#include "base/home.h"
#include "string-fun.h"
#include "base/cook.h"
#include "BreakPoint.h"

char *GDBAgent_XDB_init_commands;
char *GDBAgent_XDB_settings;

GDBAgent_XDB::GDBAgent_XDB (XtAppContext app_context,
	      const string& gdb_call):
    GDBAgent (app_context, gdb_call, XDB)
{
    _title = "XDB";
    _has_frame_command = true;
    _has_display_command = false;
    _has_clear_command = false;
    _has_pwd_command = false;
    _has_make_command = false;
    _has_regs_command = false;
    _has_named_values = false;
    _has_examine_command = false;
    _has_attach_command = false;
}

// Return true iff ANSWER ends with primary prompt.
bool GDBAgent_XDB::ends_with_prompt (const string& ans)
{
    string answer = ans;
    strip_control(answer);

    // Any line equal to `>' is a prompt.
    const unsigned beginning_of_line = answer.index('\n', -1) + 1;
    if (beginning_of_line < answer.length()
        && answer.length() > 0
        && answer[beginning_of_line] == '>')
    {
        last_prompt = ">";
        return true;
    }
    return false;
}

// Remove prompt
void GDBAgent_XDB::cut_off_prompt(string& answer) const
{
    answer = answer.before('>', -1);
}

string GDBAgent_XDB::print_command(const char *expr, bool internal) const
{
    /* UNUSED */ (void (internal)); 
    string cmd = "p";

    if (strlen(expr) != 0) {
	cmd += ' ';
	cmd += expr;
    }

    return cmd;
}

string GDBAgent_XDB::history_file() const
{
    const char *g = getenv("XDBHIST");
    if (g != 0)
        return g;
    else
	return string(gethome()) + "/.xdbhist";
}

string GDBAgent_XDB::where_command(int count) const
{
    string cmd = "t";

    if (count != 0)
	cmd += " " + itostring(count);

    return cmd;
}

string GDBAgent_XDB::info_locals_command() const { return "l"; }

string GDBAgent_XDB::pwd_command() const { return "!pwd"; }

string GDBAgent_XDB::make_command(const string& args) const
{
    string cmd = "!make";

   if (args.empty())
	return cmd;
    else
	return cmd + " " + args;
}

string GDBAgent_XDB::jump_command(const string& pos) const
{
    string pos_ = pos;

    if (pos_.contains('*', 0))
	pos_ = pos_.after('*');
    return "g " + pos_;
}

string GDBAgent_XDB::frame_command() const
{
    return print_command("$depth");
}

string GDBAgent_XDB::frame_command(int num) const
{
    return "V " + itostring(num);
}

string GDBAgent_XDB::echo_command(const string& text) const 
{
    return quote(text);
}

string GDBAgent_XDB::enable_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "ab" + bp;
}

string GDBAgent_XDB::disable_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "sb" + bp;
}

string GDBAgent_XDB::delete_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "db" + bp;
}

string GDBAgent_XDB::ignore_command(const string& bp, int count) const
{
    return "bc " + bp + " " + itostring(count);
}

string GDBAgent_XDB::debug_command(const char *program, string args) const
{
    if (!args.empty() && !args.contains(' ', 0))
	args.prepend(' ');

    return string("#file ") + program; // just a dummy
}

string GDBAgent_XDB::signal_command(int sig) const
{
    string n = itostring(sig);

    return "p $signal = " + n + "; C";
}

string GDBAgent_XDB::run_command(string args) const
{
    if (!args.empty() && !args.contains(' ', 0))
	args = " " + args;

    if (args.empty())
	return "R";
    else
	return "r" + args;
}

string GDBAgent_XDB::assign_command(const string& var, const string& expr) const
{
    string cmd = "pq";

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
void GDBAgent_XDB::parse_break_info (BreakPoint *bp, string &info) 
{
    // Actual parsing code is in BreakPoint
    bp->process_xdb (info);
}
