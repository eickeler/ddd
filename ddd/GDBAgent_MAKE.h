// GDBAgent derived class to support MAKE debugger
//
// Copyright (c) 2023 Michael J. Eager
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

class GDBAgent_MAKE: public GDBAgent {
public:
    // Constructor
    GDBAgent_MAKE (XtAppContext app_context,
	      const string& gdb_call);
    bool ends_with_prompt (const string& ans) override;
    void cut_off_prompt(string& answer) const override;
    string print_command(const char *expr, bool internal) const override;
    string print_command(const string& expr, bool internal = true) const override {
      return print_command(expr.chars(), internal);
    }
    string info_args_command() const override { return info_locals_command(); }
    string pwd_command() const override;
    string make_command(const string& target) const override;
    string kill_command() const override { return "quit"; }
    string echo_command(const string& text) const override;
    string condition_command(const string& bp, const char *expr) const override
	{ /*UNUSED*/ (void (bp)); (void (expr)); return ""; }
    string debug_command(const char *file = "", string args = "") const override;
    string assign_command(const string& var, const string& expr) const override;
};
