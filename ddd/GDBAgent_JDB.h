// GDBAgent derived class to support JDB debugger
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

extern char *GDBAgent_JDB_init_commands;
extern char *GDBAgent_JDB_settings;

class GDBAgent_JDB: public GDBAgent {
public:
    // Constructor
    GDBAgent_JDB (XtAppContext app_context,
	      const string& gdb_call);
    bool ends_with_prompt (const string& ans) override;
    bool is_exception_answer(const string& answer) const override;
    void cut_off_prompt(string& answer) const override;
    string print_command(const char *expr, bool internal=true) const override;
    string info_locals_command() const override;
    string info_args_command() const override { return info_locals_command(); }
    string pwd_command() const override;
    string watch_command(const string&, WatchMode) const override;
    string frame_command() const override { return ""; }
    string echo_command(const string& text) const override
	{ /*UNUSED*/ (void (text)); return ""; }
    string whatis_command(const string& expr) const override
	{ return "class " + expr; }
    string debug_command(const char *file = "", string args = "") const override;
    string assign_command(const string& var, const string& expr) const override;
    string init_commands() const override 
        { return GDBAgent_JDB_init_commands; }
    string settings() const override 
        { return GDBAgent_JDB_settings; }
    void parse_break_info (BreakPoint *bp, string &info) override;
};
