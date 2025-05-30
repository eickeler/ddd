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

extern char *GDBAgent_DBX_init_commands;
extern char *GDBAgent_DBX_settings;

class GDBAgent_DBX: public GDBAgent {
public:
    // Constructor
    GDBAgent_DBX (XtAppContext app_context,
	      const string& gdb_call);
    bool is_ladebug() const;
    bool ends_with_prompt (const string& ans) override;
    bool ends_with_secondary_prompt(const string& answer) const override;
    void cut_off_prompt(string& answer) const override;
    string print_command(const char *expr, bool internal=true) const override;
    string print_command(const string& expr, bool internal = true) const {
      return print_command(expr.chars(), internal);
    }
    string info_locals_command() const override;
    string info_args_command() const override { return info_locals_command(); }
    string make_command(const string& target) const override;
    string jump_command(const string& pc) const override { return "cont at " + pc; }
    string regs_command(bool all = true) const override;
    string watch_command(const string&, WatchMode) const override;
    string func_command() const override { return "func"; }
    string echo_command(const string& text) const override;
    string whatis_command(const string& expr) const override;
    string enable_command(string bp = "") const override;
    string disable_command(string bp = "") const override;
    string delete_command(string bp = "") const override;
    string ignore_command(const string& bp, int count) const override;
    string condition_command(const string& bp, const char *expr) const override
	{ /*UNUSED*/ (void (bp)); (void (expr)); return ""; }
    string shell_command(const string& cmd) const override
	{ return "sh " + cmd; }
    string debug_command(const char *file = "", string args = "") const override;
    string signal_command(int sig) const override;
    string run_command(string args) const override;
    string rerun_command() const override;
    string attach_command(int pid, const string& file) const override;
    string detach_command(int pid) const override;
    string assign_command(const string& var, const string& expr) const override;
    string init_commands() const override 
        { return GDBAgent_DBX_init_commands; }
    string settings() const override 
        { return GDBAgent_DBX_settings; }
    virtual void clean_frame_line(string &value) override;
};
