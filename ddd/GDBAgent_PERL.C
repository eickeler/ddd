// GDBAgent derived class to support PERL debugger
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
#include "GDBAgent_PERL.h"
#include "regexps.h"
#include "base/cook.h"
#include "string-fun.h"
#include "base/isid.h"

char *GDBAgent_PERL_init_commands;
char *GDBAgent_PERL_settings;

GDBAgent_PERL::GDBAgent_PERL (XtAppContext app_context,
	      const string& gdb_call):
    GDBAgent (app_context, gdb_call, PERL)
{
    _title = "Perl";
    _has_frame_command = false;
    _has_display_command = false;
    _has_jump_command = false;
    _has_regs_command = false;
    _has_named_values = false;
    _has_err_redirection = false;
    _has_examine_command = false;
    _has_attach_command = false;
    _program_language = LANGUAGE_PERL;
}

// Return true iff ANSWER ends with primary prompt.
bool GDBAgent_PERL::ends_with_prompt (const string& ans)
{
    string answer = ans;
    strip_control(answer);

    // Any line ending in `DB<N> ' is a prompt.
    // Since N does not make sense in DDD, we use `DB<> ' instead.
    //
    // "T. Pospisek's MailLists" <tpo2@sourcepole.ch> reports that
    // under Debian, Perl issues a prompt with control characters:
    // <- "\001\002  DB<1> \001\002"

#if RUNTIME_REGEX
    static regex rxperlprompt("[ \t\001\002]*DB<+[0-9]*>+[ \t\001\002]*");
#endif

    int i = answer.length() - 1;
    if (i < 1 || answer[i] != ' ' || answer[i - 1] != '>')
        return false;

    while (i > 0 && answer[i - 1] != '\n' && !answer.contains("DB", i))
        i--;

    string possible_prompt = answer.from(i);
    if (possible_prompt.matches(rxperlprompt))
    {
        last_prompt = "DB<> ";
        return true;
    }
    return false;
}

// Remove prompt
void GDBAgent_PERL::cut_off_prompt(string& answer) const
{
    int i = answer.index("DB<", -1);
    while (i > 0 && answer[i - 1] == ' ')
        i--;
    answer.from(i) = "";
}

// Write command
int GDBAgent_PERL::write_cmd(const string& cmd)
{
    if (cmd.contains("exec ", 0))
    {
	// Rename debugger
	string p = cmd.before('\n');
	p = p.after("exec ");
	if (p.contains('\'', 0) || p.contains('\"', 0))
	    p = unquote(p);
	if (!p.empty())
	    _path = p;
    }

    return write(cmd);
}

string GDBAgent_PERL::print_command(const char *expr, bool internal) const
{
    /* UNUSED */ (void (internal)); 
    string cmd = "x";

    if (strlen(expr) != 0) {
	cmd += ' ';
	cmd += expr;
    }

    return cmd;
}

string GDBAgent_PERL::where_command(int count) const
{
    string cmd = "T";

    if (count != 0)
	cmd += " " + itostring(count);

    return cmd;
}

string GDBAgent_PERL::info_locals_command() const { return "V"; }

string GDBAgent_PERL::pwd_command() const { return "p $ENV{'PWD'} || `pwd`"; }

string GDBAgent_PERL::make_command(const string& args) const
{
    if (args.empty())
	return "system 'make'";
    else
	return "system 'make " + args + "'";
}

string GDBAgent_PERL::echo_command(const string& text) const 
{
    return "print DB::OUT " + quote(text, '\"');
}

string GDBAgent_PERL::shell_command(const string& cmd) const
{
    return "system " + quote(cmd, '\'');
}

string GDBAgent_PERL::debug_command(const char *program, string args) const
{
    /* UNUSED */ (void (program)); (void (args));
    if (!args.empty() && !args.contains(' ', 0))
	args.prepend(' ');

    return "R";
}

string GDBAgent_PERL::run_command(string args) const
{
    if (!args.empty() && !args.contains(' ', 0))
	args = " " + args;

    return "exec " + quote(debugger() + " -d " + program() + args);
}

string GDBAgent_PERL::assign_command(const string& var, const string& expr) const
{
    string cmd = "";

    if (!var.empty() && !is_perl_prefix(var[0]))
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

// A PERL hash key can contain spaces. If we try to strip the
// qualifiers, the key name will be the word after the last space
// in the key name:
// 'my key' will be returned as 'key'
// This has several effects:
// 1. The key name is displayed incorrectly
// 2. Since the key name is wrong, you can't access the associated
//    value trough the Display Data window.
// 3. Could lead to display a value associated to a valid key
// so, turn it OFF.

string GDBAgent_PERL::clean_member_name (string member_name,
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

void GDBAgent_PERL::clean_history_line (string &line)
{
    line = line.after(" -d ");
    line = line.before('\"');
    if (line.contains(rxwhite))
        line = line.before(rxwhite);
}

