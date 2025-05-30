// $Id$ -*- C++ -*-
// Communicate with separate GDB process

// Copyright (C) 1995 Technische Universitaet Braunschweig, Germany.
// Copyright (C) 2000 Universitaet Passau, Germany.
// Copyright (C) 2003-2025 Free Software Foundation, Inc.
// Written by Dorothea Luetkehaus <luetke@ips.cs.tu-bs.de>
// and Andreas Zeller <zeller@gnu.org>.
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

//-----------------------------------------------------------------------------
// A GDBAgent creates a connection to an inferior GDB via a TTYAgent.
// There are two ways to send commands to GDB:
// 1. send_user_cmd: is used for user input at the GDB prompt.  GDB output
//    (partial answers) are processed immediately.
// 2. send_qu_array: issues a list of queries to GDB.  The passed function
//    is called as soon as the last query is processed.  The passed function
//    must free the memory claimed by the query array.
//-----------------------------------------------------------------------------

#ifndef _DDD_GDBAgent_h
#define _DDD_GDBAgent_h

#include "AppData.h"
#include "agent/TTYAgent.h"
#include "agent/HandlerL.h"
#include "base/strclass.h"
#include "base/bool.h"
#include "base/assert.h"
#include "template/VoidArray.h"

#include <vector>

//-----------------------------------------------------------------------------
// Debugger types
//-----------------------------------------------------------------------------

enum DebuggerType { BASH, DBG, DBX, GDB, JDB, PERL, PYDB, XDB, MAKE };
enum DebuggerCPU { cpu_intel, cpu_unknown};
//-----------------------------------------------------------------------------
// Program language
//-----------------------------------------------------------------------------

#ifdef LANGUAGE_C
#undef LANGUAGE_C		// DEC defines this
#endif

enum ProgramLanguage { 
    LANGUAGE_ADA,		// Ada (GNAT), as supported by GDB
    LANGUAGE_BASH,		// Bash, as supported by bashdb.
    LANGUAGE_C,			// C-like: C, C++
    LANGUAGE_CHILL,		// Chill, as supported by GDB.
    LANGUAGE_FORTRAN,		// FORTRAN, as supported by GDB.
    LANGUAGE_JAVA,		// Java, as supported by GDB.
    LANGUAGE_MAKE,		// Make, as supported by remake.
    LANGUAGE_PASCAL,		// Pascal-like: Pascal, Modula...
    LANGUAGE_PERL,		// Perl, as supported by Perl.
    LANGUAGE_PHP,		// PHP, as supported by DBG.
    LANGUAGE_PYTHON,		// Python, as supported by PYDB.
    LANGUAGE_OTHER		// Others
};

//-----------------------------------------------------------------------------
// Watch modes
//-----------------------------------------------------------------------------

typedef int WatchMode;

const int WATCH_CHANGE = 1;	// break if value changes
const int WATCH_READ   = 2;	// break if value is read
const int WATCH_WRITE  = 4;	// break if value is written

const int WATCH_ACCESS = WATCH_READ | WATCH_WRITE; // shorthand

//-----------------------------------------------------------------------------
// Procedure types.
//-----------------------------------------------------------------------------

// Called as soon as an ANSWER on send_user_cmd (or a part of it)
// is received
typedef void (* OAProc) (const string& answer,
			 void* user_data);

// Called after the whole answer to send_user_cmd has been received
typedef void (* OACProc) (void* user_data);

// Called from send_qu_array with the complete answers
typedef void (* OQACProc) (std::vector<string>& complete_answers,
			   const VoidArray& user_datas,
			   void *user_data);

//-----------------------------------------------------------------------------

// Create appropriate call for the given debugger
string build_gdb_call(DebuggerType debugger_type,
		      const string& debugger_command,
		      const string& init_file,
		      int argc, char *argv[],
		      string myArguments = "");

// Handlers
const unsigned ReadyForQuestion = TTYAgent_NTypes;
const unsigned ReadyForCmd      = ReadyForQuestion + 1;
const unsigned LanguageChanged  = ReadyForCmd + 1;
const unsigned ReplyRequired    = LanguageChanged + 1;
const unsigned YesNoRequired    = ReplyRequired + 1;
const unsigned EchoDetected     = YesNoRequired + 1;
const unsigned AsyncAnswer      = EchoDetected + 1;
const unsigned ExceptionState   = AsyncAnswer + 1;
const unsigned Recording        = ExceptionState + 1;
const unsigned GDBAgent_NTypes  = Recording + 1;

// Handler info
struct ReplyRequiredInfo {
    string question;		// Question asked by GDB
    string reply;		// Our reply

    ReplyRequiredInfo()
	: question(), reply()
    {}
};

//-----------------------------------------------------------------------------
// The GDBAgent class.
//-----------------------------------------------------------------------------

class GDBAgent: public TTYAgent {
public:
    DECLARE_TYPE_INFO
    DebuggerCPU cpu;

protected:
    enum State {
	ReadyWithPrompt,
	BusyOnCmd, 
	BusyOnQuArray,
	BusyOnInitialCmds
    };
    State state;		// Current state

    DebuggerType    _type;	// Debugger type
    void*           _user_data;	// used in callbacks etc.

    bool _has_frame_command;	// Debugger properties
    bool _has_func_command;	
    bool _has_file_command;
    bool _has_run_io_command;
    bool _has_print_r_option;	// FIXME:  Is this used?
    bool _has_output_command;
    bool _has_where_h_option;	// FIXME:  Is this used?
    bool _has_display_command;
    bool _has_clear_command;
    bool _has_handler_command;
    bool _has_pwd_command;
    bool _has_setenv_command;
    bool _has_edit_command;
    bool _has_make_command;
    bool _has_jump_command;
    bool _has_regs_command;
    WatchMode _has_watch_command;
    bool _has_named_values;
    bool _has_when_command;
    bool _has_when_semicolon;
    bool _wants_delete_comma;
    bool _has_err_redirection;
    bool _has_givenfile_command;
    bool _has_cont_sig_command;
    bool _has_examine_command;
    bool _has_rerun_command;
    bool _rerun_clears_args;
    bool _has_attach_command;
    bool _has_addproc_command;
    bool _has_debug_command;
    bool _is_windriver_gdb;

    ProgramLanguage _program_language; // Current program language

    bool _verbatim;		// True if in verbatim mode
    bool _recording;		// True if we are recording commands
    bool _detect_echos;		// True if echos are to be detected
    bool _buffer_gdb_output;	// True if GDB output is to be buffered
    bool _flush_next_output;	// True if next GDB output is to be flushed

    string last_prompt;		// Last prompt received
    string last_written;	// Last command sent
    string _title;		// Name of debugger
    int echoed_characters;      // # of echoed characters so far (-1: no echo)

    bool exception_state;	// True if exception encountered

    GDBAgent& operator = (const GDBAgent&);

protected:
    // Return PREFIX + EXPR, parenthesizing EXPR if needed
    static string prepend_prefix(const string& prefix, const string& expr);
    static string prepend_prefix(const char *prefix, const string& expr);

    // Return EXPR + SUFFIX, parenthesizing EXPR if needed
    static string append_suffix(const string& expr, const string& suffix);
    static string append_suffix(const string& expr, const char *suffix);

    // General trace function
    void trace(const char *prefix, void *call_data) const;

    // Perl specials
    static void munch_perl_array(string& value, bool hash);
    static void munch_perl_scalar(string& value);

public:
    // Constructor
    GDBAgent (XtAppContext app_context,
	      const string& gdb_call,
	      DebuggerType type,
	      unsigned nTypes = GDBAgent_NTypes);

    // Duplicator
    GDBAgent (const GDBAgent& gdb);
    virtual Agent *dup() const { return new GDBAgent(*this); }

    ~GDBAgent ();

    static
    GDBAgent* Create (XtAppContext app_context,
	      const string& gdb_call,
	      DebuggerType type);

    // Start new process
    void do_start (OAProc  on_answer,
		   OACProc on_answer_completion,
		   void*   user_data);

    // After receiving the first GDB prompt, send commands to GDB.
    // Processing is very much like send_user_cmd_plus.
    void start_plus (OAProc   on_answer,
		     OACProc  on_answer_completion,
		     void*    user_data,
		     const std::vector<string>& cmds,
		     const VoidArray& user_datas,
		     int      qu_count,
		     OQACProc on_qu_array_completion,
		     void*    qa_data,
		     bool&    qa_data_registered);

    // true iff command was sent.
    // If user_data == 0, _user_data remains unchanged.
    bool send_user_cmd      (string cmd, void* user_data = 0);  
    bool send_user_ctrl_cmd (const string& cmd, void* user_data = 0);


    // Order of tasks:
    // 1. Send USER_CMD to GDB, as in send_user_cmd
    //    (state: ReadyWithPrompt --> BusyOnCmd)
    // 2. Call OAProc when answer comes in
    //    (state:BusyOnCmd --> BusyOnQuArray)
    // 3. Send CMDS, as in send_qu_array.
    // 4. When all replies have come in: call OACProc and OQACProc.
    //
    bool send_user_cmd_plus (const std::vector<string>& cmds,
			     const VoidArray& qu_datas,
			     int      qu_count,
			     OQACProc on_qu_array_completion,
			     void*    qa_data,
			     bool&    qa_data_registered,
			     string user_cmd,
			     void* user_data = 0);

    bool send_qu_array (const std::vector<string>& cmds,
			const VoidArray& qu_datas,
			int      qu_count,
			OQACProc on_qu_array_completion,
			void*    qa_data,
			bool&    qa_data_registered);


    // Resources
    DebuggerType type()       const { return _type; }
    bool isSunDBX()           const {
#ifdef HAVE_SUNDBX
                                      return type() == DBX;
#else
                                      return false;
#endif
    }
    const string title()      const { return _title; }
    bool isReadyWithPrompt()  const { return state == ReadyWithPrompt; }
    const string& prompt()    const { return last_prompt; }


    // Debugger properties
    // True if debugger has `frame' command
    bool has_frame_command() const    { return _has_frame_command; }	
    bool has_frame_command(bool val)  { return _has_frame_command = val; }

    // True if debugger has `file' command
    bool has_file_command() const    { return _has_file_command; }
    bool has_file_command(bool val)  { return _has_file_command = val; }

    // True if debugger has `func' command
    bool has_func_command() const    { return _has_func_command; }	
    bool has_func_command(bool val)  { return _has_func_command = val; }

    // True if debugger has `run_io' command
    bool has_run_io_command() const    { return _has_run_io_command; }
    bool has_run_io_command(bool val)  { return _has_run_io_command = val; }

    // True if debugger has `-r' option in `print' and `display'
    bool has_print_r_option() const   { return _has_print_r_option; }
    bool has_print_r_option(bool val) { return _has_print_r_option = val; }

    // True if debugger has `output' command
    bool has_output_command() const   { return _has_output_command; }
    bool has_output_command(bool val) { return _has_output_command = val; }

    // True if debugger has `-h' option in `where'
    bool has_where_h_option() const   { return _has_where_h_option; }
    bool has_where_h_option(bool val) { return _has_where_h_option = val; }

    // True if debugger has `display' command
    bool has_display_command() const   { return _has_display_command; }
    bool has_display_command(bool val) { return _has_display_command = val; }

    // True if debugger has `clear' command
    bool has_clear_command() const     { return _has_clear_command; }
    bool has_clear_command(bool val)   { return _has_clear_command = val; }

    // True if debugger has `handler' command
    bool has_handler_command() const   { return _has_handler_command; }
    bool has_handler_command(bool val) { return _has_handler_command = val; }

    // True if debugger has `pwd' command
    bool has_pwd_command() const       { return _has_pwd_command; }
    bool has_pwd_command(bool val)     { return _has_pwd_command = val; }

    // True if debugger has `setenv' command
    bool has_setenv_command() const    { return _has_setenv_command; }
    bool has_setenv_command(bool val)  { return _has_setenv_command = val; }

    // True if debugger has `edit' command
    bool has_edit_command() const      { return _has_edit_command; }
    bool has_edit_command(bool val)    { return _has_edit_command = val; }

    // True if debugger has `make' command
    bool has_make_command() const      { return _has_make_command; }
    bool has_make_command(bool val)    { return _has_make_command = val; }

    // True if debugger has `jump' command
    bool has_jump_command() const      { return _has_jump_command; }
    bool has_jump_command(bool val)    { return _has_jump_command = val; }

    // True if debugger has `regs' command
    bool has_regs_command() const      { return _has_regs_command; }
    bool has_regs_command(bool val)    { return _has_regs_command = val; }

    // Non-zero if debugger has `watch' command; also indicates
    // `watch' capabilities
    WatchMode has_watch_command() const { return _has_watch_command; }
    WatchMode has_watch_command(WatchMode val)
    { 
	return _has_watch_command = val;
    }

    // True if debugger issues `NAME = VALUE' upon `print' commands
    bool has_named_values() const      { return _has_named_values; }
    bool has_named_values(bool val)    { return _has_named_values = val; }

    // True if debugger has `when' command
    bool has_when_command() const      { return _has_when_command; }
    bool has_when_command(bool val)    { return _has_when_command = val; }

    // True if debugger wants `;' at the end of `when' command specs
    bool has_when_semicolon() const    { return _has_when_semicolon; }
    bool has_when_semicolon(bool val)  { return _has_when_semicolon = val; }

    // True if debugger wants events separated by `,'
    bool wants_delete_comma() const      { return _wants_delete_comma; }
    bool wants_delete_comma(bool val)    { return _wants_delete_comma = val; }

    // True if debugger has stderr redirection using `>&'
    bool has_err_redirection() const   { return _has_err_redirection; }
    bool has_err_redirection(bool val) { return _has_err_redirection = val; }

    // True if debugger has `givenfile' command
    bool has_givenfile_command() const   { return _has_givenfile_command; }
    bool has_givenfile_command(bool val) 
    {
	return _has_givenfile_command = val;
    }

    // True if debugger has `cont sig' command
    bool has_cont_sig_command() const   { return _has_cont_sig_command; }
    bool has_cont_sig_command(bool val) { return _has_cont_sig_command = val; }

    // True if debugger has `examine' or `x' command
    bool has_examine_command() const   { return _has_examine_command; }
    bool has_examine_command(bool val) { return _has_examine_command = val; }

    // True if debugger has `rerun' command
    bool has_rerun_command() const   { return _has_rerun_command; }
    bool has_rerun_command(bool val) { return _has_rerun_command = val; }

    // True if `rerun' command clears current arguments
    bool rerun_clears_args() const   { return _rerun_clears_args; }
    bool rerun_clears_args(bool val) { return _rerun_clears_args = val; }

    // True if debugger has `attach' command
    bool has_attach_command() const   { return _has_attach_command; }
    bool has_attach_command(bool val) { return _has_attach_command = val; }

    // True if debugger has `addproc' command
    bool has_addproc_command() const   { return _has_addproc_command; }
    bool has_addproc_command(bool val) { return _has_addproc_command = val; }

    // True if debugger has `debug' command
    bool has_debug_command() const   { return _has_debug_command; }
    bool has_debug_command(bool val) { return _has_debug_command = val; }

    // True if debugger is the Windriver variant of GDB
    bool is_windriver_gdb() const   { return _is_windriver_gdb; }
    bool is_windriver_gdb(bool val) { return _is_windriver_gdb = val; }

    // Current program language
    ProgramLanguage program_language() const   { return _program_language; }
    ProgramLanguage program_language(ProgramLanguage val) 
    {
	if (_program_language != val)
	{
	    _program_language = val;
	    callHandlers(LanguageChanged, (void *)val);
	}
	return program_language();
    }
    ProgramLanguage program_language(string text);

    // True if debugger can enable breakpoints
    bool has_disassembly() const
    { 
      return type() == GDB 
	// || type() == PYDB  // In theory this could be done.
	;
    }

    // True if debugger can enable breakpoints
    bool has_enable_command() const
    { 
      return type() == BASH || type() == DBG || type() == GDB  
	|| type() == PYDB || type() == XDB || has_handler_command();
    }
    bool has_disable_command() const
    {
	return has_enable_command();
    }

    // True if debugger can set ignore counts on breakpoints
    bool has_ignore_command() const
    {
	return type() == DBG || type() == GDB || type() == PYDB 
	    || type() == XDB || has_handler_command();
    }

    // True if debugger can set conditions on breakpoints
    bool has_condition_command() const
    {
      return type() == BASH || type() == DBG || type() == GDB 
  	  || type() == PYDB ;
    }

    // True if debugger can delete breakpoints by number
    bool has_delete_command() const
    {
      return type() == BASH || type() == DBG || type() == DBX || type() == GDB 
	  || type() == PYDB || type() == XDB ;
    }

    // True if debugger has volatile breakpoints (i.e. breakpoints may
    // change at any time)
    bool has_volatile_breakpoints() const
    {
	return type() == DBG  || type() == DBX  || type() == GDB 
	  ||   type() == MAKE || type() == PERL || type() == PYDB 
	  ||   type() == XDB;
    }

    // True if debugger supports I/O redirection
    bool has_redirection() const
    {
	return type() == GDB || type() == XDB || 
	       type() == DBX || type() == PERL;
    }

    // True if debugger supports assignments
    bool has_assign_command() const
    {
	// All debuggers except JDB 1.1 can assign
	return !(type() == JDB && has_debug_command());
    }

    // True if debugger supports calling system functions
    bool has_system_calls() const
    {
	return type() == GDB || type() == XDB || type() == DBX || 
	  type() == PYDB || type() == PERL;
    }

    // True if debugger supports loading and examining executables
    bool has_exec_files() const
    {
	return type() == GDB || type() == XDB || type() == DBX;
    }

    // True if debugger supports loading and examining classes
    bool has_classes() const
    {
	return type() == JDB;
    }

    // True if debugger supports loading and examining core files
    bool has_core_files() const
    {
	return type() == GDB || type() == XDB || type() == DBX;
    }

    // True if debugger supports separate processes (attach, detach)
    bool has_processes() const
    {
	return type() == GDB || type() == XDB || type() == DBX;
    }

    // True if debugger supports `cd'
    bool has_cd_command() const
    {
      return type() == BASH || type() == GDB || type() == DBX 
	|| type() == PERL || type() == PYDB  || type() == XDB;
    }

    // True if debugger supports `shell'
    bool has_shell_command() const
    {
      return type() == BASH 
	|| type() == DBX 
	|| type() == GDB 
	|| type() == PERL 
	|| type() == PYDB
	|| type() == MAKE
	|| type() == XDB;
    }

    // True if debugger has numbered breakpoints
    bool has_numbered_breakpoints() const
    {
      return type() == BASH || type() == DBG || type() == DBX || type() == GDB
	  || type() == PYDB || type() == XDB;
    }

    // True if debugger supports temporary breakpoints
    bool has_temporary_breakpoints() const
    {
      return type() == BASH || type() == DBG  || type() == GDB 
	  || type() == PERL || type() == PYDB || type() == XDB 
	  || has_when_command() ;
    }

    // True if debugger supports breakpoint conditions
    bool has_breakpoint_conditions() const
    {
      return type() == BASH || type() == DBG  || type() == DBX 
	  || type() == GDB  || type() == PERL || type() == PYDB 
 	  || type() == XDB;
    }

    // True if debugger supports breakpoint commands
    bool has_breakpoint_commands() const
    {
        return type() == BASH || type() == GDB 
	  || type() == MAKE || has_when_command() || type() == PERL 
	  || type() == PYDB || type() == XDB 
	  ;
    }

    // True if debugger has typed pointers, as in `(TYPE)0x0'
    bool has_typed_pointers() const
    {
	return type() == GDB || type() == JDB;
    }

    // True if debugger has typed structs, as in `(TYPE)0x1234 { ... }'
    bool has_typed_structs() const
    {
	return type() == JDB;
    }

    // True if debugger uses `(scalar = ...)' for out-of-range enumerations
    bool has_scalars() const
    {
	return type() == DBX;
    }

    // True if debugger can use quotes for complex expressions
    bool has_quotes() const
    {
	return type() == GDB;
    }

    // True if `display X' automatically prints X
    bool display_prints_values() const
    {
      return type() == GDB || type() == PYDB ;
    }

    // True if debugger can enable displays
    bool has_enable_display_command() const
    {
	return type() == GDB || type() == PYDB || type() == DBG;
    }
    bool has_disable_display_command() const
    {
	return has_enable_display_command();
    }

    // True if debugger has numbered displays
    bool has_numbered_displays() const
    {
	return type() == GDB || type() == PYDB || type() == DBG;
    }

    // True if debugger wants displays separated by `,'
    bool wants_display_comma() const
    {
	return type() == DBX;
    }

    // True if debugger has `info displays' command
    bool has_info_display_command() const
    {
	return !display_command().empty();
    }

    // True if `undisplay' redisplays remaining values
    bool has_redisplaying_undisplay() const
    {
	return type() == DBX;
    }

    // True if debugger supports breakpoint conditions
    bool has_conditions() const
    {
	return has_condition_command() || type() != JDB;
    }

    // True if arrays are contained in braces
    bool has_array_braces() const { return !is_ladebug(); }

    // True if debugger can disable breakpoints
    bool can_disable() const
    {
	return has_disable_command() || has_conditions();
    }

    // True if debugger can enable breakpoints
    bool can_enable() const
    {
	return has_enable_command() || has_conditions();
    }

    // True if Ladebug
    bool is_ladebug() const
    {
	return false;
    }

    // True if a minimum indent is required.  This is true for
    // scripting languages.
    bool requires_script_indent() const
    {
	return program_language() == LANGUAGE_PERL ||
	    program_language() == LANGUAGE_PYTHON;
    }

    // True if DBX output is to be processed verbatim
    bool verbatim() const        { return _verbatim; }
    bool verbatim(bool val)      { return _verbatim = val; }

    // True if we are recording commands
    bool recording() const         { return _recording; }
    bool recording(bool val);

    // True if checking for echos
    bool detect_echos() const        { return _detect_echos; }
    bool detect_echos(bool val)      { return _detect_echos = val; }

    // True if buffering partial answers
    bool buffer_gdb_output() const       { return _buffer_gdb_output; }
    bool buffer_gdb_output(bool val)     { return _buffer_gdb_output = val; }

    // True if next answer is to be flushed
    bool flush_next_output() const       { return _flush_next_output; }
    bool flush_next_output(bool val)     { return _flush_next_output = val; }

    // Place quotes around filename FILE if needed
    string quote_file(const string& file) const;

    // Several commands
				                    // GDB command
						    // -----------------------
    virtual string print_command(const char *expr = "",     // print|output EXP
			 bool internal = true) const
    {
	/* UNUSED */ (void (expr));
	/* UNUSED */ (void (internal));
	assert (0);	/* Should never be called. */
    }
    virtual string print_command(const string& expr,
			 bool internal = true) const {
      return print_command(expr.chars(), internal);
    }
    virtual string assign_command(const string& var,        // set variable VAR = EXPR
			  const string& expr) const
	{ /*UNUSED*/ (void (var)); (void (expr)); return ""; }
    string display_command(const char *expr = "") const; // display EXPR
    string display_command(const string& expr) const {
      return display_command(expr.chars());
    }
    virtual string where_command(int count = 0) const;
    virtual string pwd_command() const;	                    // pwd
    virtual string frame_command(int num) const;
    virtual string relative_frame_command(int offset) const;// up|down OFFSET
    virtual string frame_command() const;	    // frame
    virtual string func_command() const { return frame_command(); }
    virtual string echo_command(const string& text) const;
    virtual string whatis_command(const string& expr) const
	{ /*UNUSED*/ (void (expr)); return ""; }
    string dereferenced_expr(const string& expr) const;    // *EXPR
    string address_expr(string expr) const;         // &EXPR
    string index_expr(const string& expr, const string& index) const; // EXPR[INDEX]
    int default_index_base() const;                 // 0 in C, else 1
    string member_separator() const;                // " = " in C

    virtual string info_locals_command() const { return "info locals"; }
    virtual string info_args_command() const { return "info args"; }
    virtual string info_display_command() const { return display_command(); }
    string disassemble_command(string start, const char *end = "") const;
                                                    // disassemble START END
    string disassemble_command(const string &start, const string& end ) const {
      return disassemble_command(start, end.chars() );
    }
    virtual string make_command(const string& args) const { /*UNUSED*/ (void (args)); return ""; }
    virtual string jump_command(const string& pc) const { /*UNUSED*/ (void (pc)); return ""; }
    virtual string regs_command(bool all = true) const { /*UNUSED*/ (void (all)); return ""; }
    virtual string watch_command(const string& expr, WatchMode w = WATCH_CHANGE) const {
	/*UNUSED*/ (void (expr)); (void (w)); return "";
    } // watch EXPR
    virtual string kill_command() const { return "kill"; }                    // kill
    virtual string enable_command(string bp = "") const { /*UNUSED*/ (void (bp)); return ""; }
    virtual string disable_command(string bp = "") const { /*UNUSED*/ (void (bp)); return ""; }
    virtual string delete_command(string bp = "") const { /*UNUSED*/ (void (bp)); return ""; }
    virtual string ignore_command(const string& bp, int count) const
	{ /*UNUSED*/ (void (bp)); (void (count)); return ""; }
    virtual string condition_command(const string& bp, const string& expr) const
	{ return condition_command(bp, expr.chars() ); }
    virtual string condition_command(const string& bp, const char *expr) const
	{ /*UNUSED*/ (void (bp)); (void (expr)); return ""; }
    virtual string shell_command(const string& cmd) const
	{ return "shell " + cmd; }
    virtual string debug_command(const char *file = "",          // file FILE
			 string args = "") const
	{ /*UNUSED*/ (void (file)); (void (args)); return ""; }
    virtual string debug_command(const string& file, string args = "") const {
      return debug_command( file.chars(), args );
    }
    virtual string signal_command(int sig) const { /*UNUSED*/ (void (sig)); return ""; }
    string nop_command(const char *comment = "") const;  // # comment
    string nop_command(const string& comment) const {
      return nop_command(comment.chars());
    }

    // Bring VALUE of VAR into a form understood by DDD
    void munch_value(string& value, const string& var) const;

    // Split a Perl variable into its components
    static void split_perl_var(const string& var,
			       string& prefix, string& package, string& name);

    // Run program with given arguments
    virtual string run_command(string args) const 
	{ return "run" + args; }

    // Run program, re-using current arguments
    virtual string rerun_command() const { return "run"; }

    // Attach to process id PID
    virtual string attach_command(int pid, const string& file) const
	{ /*UNUSED*/ (void (pid)); (void (file)); return ""; }
    virtual string detach_command(int pid) const                
	{ /*UNUSED*/ (void (pid)); return ""; }

    // Default history file
    virtual string history_file() const { return ""; }

    // Send DATA to process
    virtual int write(const char *data, int length);

    // Custom function
    int write(const string& data)
    {
	return write(data.chars(), data.length());
    }

    // Write a command (not debuggee interaction or control characters)
    virtual int write_cmd(const string& cmd) { return write(cmd); }

    // True if ANSWER ends in a prompt
    virtual bool ends_with_prompt(const string& answer);
    virtual bool ends_with_secondary_prompt(const string& answer) const
    { 
	/* Unused */ (void (answer));
	return false;
    }
    virtual void cut_off_prompt(string& answer) const
    { 
	/* Unused */ (void (answer));
    }
    bool ends_with_yn(const string& answer) const;

    // True if exception error message
    virtual bool is_exception_answer(const string& answer) const
    { 
	/* Unused */ (void (answer));
	return false;
    }
    void set_exception_state(bool state);

    // Return target init commands
    virtual string init_commands() const { return ""; }

    // Return target settings 
    virtual string settings() const { return ""; }

    // Clean up frame line
    virtual void clean_frame_line(string &value) {
	/* Unused */ (void (value));
    }

    // Helpers
    string cmd() const;		// Actual command being executed
    string debugger() const;	// Debugger of command
    string args() const;	// Debugger args of command
    string program() const;	// Program from debugger args

private:
    bool questions_waiting;

    void* _qu_data;

    int     qu_index;
    int    _qu_count;
    std::vector<string> cmd_array;
    std::vector<string> complete_answers;
    VoidArray _qu_datas;
    void*   _qa_data;

    OAProc   _on_answer;
    OACProc  _on_answer_completion;
    OQACProc _on_qu_array_completion;

    void    init_qu_array (const std::vector<string>& cmds,
			   const VoidArray& qu_datas,
			   int      qu_count,
			   OQACProc on_qu_array_completion,
			   void*    qa_data);

    string requires_reply(const string& answer);

    void strip_dbx_comments(string& answer) const;

    void normalize_answer(string& answer) const;
    void normalize_address(string& addr) const;

    void handle_echo(string& answer);
    void handle_more(string& answer);
    void handle_reply(string& answer);
    void handle_input(string& answer);
    void handle_died();

protected:
    string complete_answer;
    void strip_control(string& answer) const;

    static void InputHP  (Agent *, void *, void *);
    static void PanicHP  (Agent *, void *, void *);
    static void StrangeHP(Agent *, void *, void *);
    static void DiedHP   (Agent *, void *, void *);

    static void traceInputHP (Agent *, void *, void *);
    static void traceOutputHP(Agent *, void *, void *);
    static void traceErrorHP (Agent *, void *, void *);

public:    
    // Terminator
    virtual void abort();
};

#endif // _DDD_GDBAgent_h
// DON'T ADD ANYTHING BEHIND THIS #endif
