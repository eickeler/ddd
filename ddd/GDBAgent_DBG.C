// GDBAgent derived class to support DBG debugger
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
#include "GDBAgent_DBG.h"
#include "base/cook.h"

char *GDBAgent_DBG_init_commands;
char *GDBAgent_DBG_settings;

#define DBG_PROMPT "dbg>"

GDBAgent_DBG::GDBAgent_DBG (XtAppContext app_context,
	      const string& gdb_call):
    GDBAgent (app_context, gdb_call, DBG)
{
    _title = "DBG";
    _has_make_command = false;
    _has_jump_command = false;
    _has_regs_command = false;
    _has_examine_command = false;
    _has_attach_command = false;
    _program_language = LANGUAGE_PHP;
}

// Return true iff ANSWER ends with primary prompt.
bool GDBAgent_DBG::ends_with_prompt (const string& ans)
{
    string answer = ans;
    strip_control(answer);

    unsigned beginning_of_line = answer.index('\n', -1) + 1;
    if ( beginning_of_line < answer.length()
        && answer.length() > 0
        && answer.matches(DBG_PROMPT,beginning_of_line)) 
    {
        recording(false);
        last_prompt = DBG_PROMPT;
        return true;
    }
    return false;
}

// Remove DBG prompt
void GDBAgent_DBG::cut_off_prompt(string& answer) const
{
    int i = answer.index(DBG_PROMPT, -1);
    while (i > 0 && answer[i - 1] == ' ')
        i--;
    answer = answer.before(i);
}

string GDBAgent_DBG::print_command(const char *expr, bool internal) const
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

string GDBAgent_DBG::info_locals_command() const { return ""; }

string GDBAgent_DBG::enable_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "enable" + bp;
}

string GDBAgent_DBG::disable_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "disable" + bp;
}

string GDBAgent_DBG::delete_command(string bp) const
{
    if (!bp.empty())
	bp.prepend(' ');

    return "delete" + bp;
}

string GDBAgent_DBG::debug_command(const char *program, string args) const
{
    if (!args.empty() && !args.contains(' ', 0))
	args.prepend(' ');

    return string("file ") + program;
}

string GDBAgent_DBG::assign_command(const string& var, const string& expr) const
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

string GDBAgent_DBG::clean_member_name (string member_name,
                                        bool &strip_qualifiers) 
{
    if (member_name.contains('\'', 0) && member_name.contains('\'', -1))
    {
        // Some Perl debugger flavours quote the member name.
        member_name = unquote(member_name);
    }
    strip_qualifiers = false;
    return member_name;
}

