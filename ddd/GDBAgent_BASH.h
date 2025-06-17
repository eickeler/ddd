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

extern char *GDBAgent_BASH_init_commands;
extern char *GDBAgent_BASH_settings;

class GDBAgent_BASH: public GDBAgent {
public:
    // Constructor
    GDBAgent_BASH (XtAppContext app_context,
	      const string& gdb_call);
    bool ends_with_prompt (const string& ans) override;
    void cut_off_prompt(string& answer) const override;
    string print_command(const char *expr, bool internal=true) const override;
    string info_locals_command() const override;
    string info_display_command() const override { return "info display"; }
    string pwd_command() const override;
    string make_command(const string& target) const override;
    string watch_command(const string&, WatchMode) const override;
    string kill_command() const override { return "quit"; }
    string echo_command(const string& text) const override;
    string enable_command(string bp = "") const override;
    string disable_command(string bp = "") const override;
    string delete_command(string bp = "") const override;
    string condition_command(const string& bp, const char *expr) const override
	{ return "condition " + bp + " " + expr; }
    string debug_command(const char *file = "", string args = "") const override;
    string assign_command(const string& var, const string& expr) const override;
    string init_commands() const override 
        { return GDBAgent_BASH_init_commands; }
    string settings() const override 
        { return GDBAgent_BASH_settings; }
    void parse_break_info (BreakPoint *bp, string &info) override;
};
