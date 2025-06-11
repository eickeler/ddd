// $Id$
// Communicate with separate GDB process

// Copyright (C) 1995-1999 Technische Universitaet Braunschweig, Germany.
// Copyright (C) 1999-2001 Universitaet Passau, Germany.
// Copyright (C) 2001-2025 Free Software Foundation, Inc.
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

char GDBAgent_rcsid[] =
    "$Id$";

// From: hobson@pipper.enet.dec.com
// Subject: And the Twelve Bugs of Christmas ....
// Keywords: topical, heard it, computers, chuckle, originally
//           appeared in fourth quarter, 1992
// Newsgroups: rec.humor.funny.reruns
// Date: Tue, 23 Dec 97 13:20:02 EST
// 
// For the first bug of Christmas, my manager said to me
//      See if they can do it again.
// 
// For the second bug of Christmas, my manager said to me
//      Ask them how they did it and
//      See if they can do it again.
// 
// For the third bug of Christmas, my manager said to me
//      Try to reproduce it
//      Ask them how they did it and
//      See if they can do it again.
// 
// For the fourth bug of Christmas, my manager said to me
//      Run with the debugger
//      Try to reproduce it
//      Ask them how they did it and
//      See if they can do it again.
// 
// For the fifth bug of Christmas, my manager said to me
//      Ask for a dump
//      Run with the debugger
//      Try to reproduce it
//      Ask them how they did it and
//      See if they can do it again.
// 
// For the sixth bug of Christmas, my manager said to me
//      Reinstall the software
//      Ask for a dump
//      Run with the debugger
//      Try to reproduce it
//      Ask them how they did it and
//      See if they can do it again.
// 
// For the seventh bug of Christmas, my manager said to me
//      Say they need an upgrade
//      Reinstall the software
//      Ask for a dump
//      Run with the debugger
//      Try to reproduce it
//      Ask them how they did it and
//      See if they can do it again.
// 
// For the eighth bug of Christmas, my manager said to me
//      Find a way around it
//      Say they need an upgrade
//      Reinstall the software
//      Ask for a dump
//      Run with the debugger
//      Try to reproduce it
//      Ask them how they did it and
//      See if they can do it again.
// 
// For the ninth bug of Christmas, my manager said to me
//      Blame it on the hardware
//      Find a way around it
//      Say they need an upgrade
//      Reinstall the software
//      Ask for a dump
//      Run with the debugger
//      Try to reproduce it
//      Ask them how they did it and
//      See if they can do it again.
// 
// For the tenth bug of Christmas, my manager said to me
//      Change the documentation
//      Blame it on the hardware
//      Find a way around it
//      Say they need an upgrade
//      Reinstall the software
//      Ask for a dump
//      Run with the debugger
//      Try to reproduce it
//      Ask them how they did it and
//      See if they can do it again.
// 
// For the eleventh bug of Christmas, my manager said to me
//      Say it's not supported
//      Change the documentation
//      Blame it on the hardware
//      Find a way around it
//      Say they need an upgrade
//      Reinstall the software
//      Ask for a dump
//      Run with the debugger
//      Try to reproduce it
//      Ask them how they did it and
//      See if they can do it again.
// 
// For the twelfth bug of Christmas, my manager said to me
//      Tell them it's a feature
//      Say it's not supported
//      Change the documentation
//      Blame it on the hardware
//      Find a way around it
//      Say they need an upgrade
//      Reinstall the software
//      Ask for a dump
//      Run with the debugger
//      Try to reproduce it
//      Ask them how they did it and
//      See if they can do it again.

//-----------------------------------------------------------------------------
// GDBAgent implementation
//-----------------------------------------------------------------------------

#include "config_data.h"
#include "GDBAgent.h"
#include "GDBAgent_BASH.h"
#include "GDBAgent_DBG.h"
#include "GDBAgent_DBX.h"
#include "GDBAgent_GDB.h"
#include "GDBAgent_JDB.h"
#include "GDBAgent_MAKE.h"
#include "GDBAgent_PERL.h"
#include "GDBAgent_PYDB.h"
#include "GDBAgent_XDB.h"
#include "base/cook.h"
#include "ddd.h"
#include "string-fun.h"
#include "regexps.h"
#include "index.h"
#include "base/isid.h"
#include "base/home.h"
#include "value-read.h"		// read_token
#include "base/casts.h"

#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <ctype.h>
#include <time.h>

#ifndef EXIT_SUCCESS
#define EXIT_SUCCESS 0
#endif

#ifndef EXIT_FAILURE
#define EXIT_FAILURE 1
#endif


DEFINE_TYPE_INFO_1(GDBAgent, TTYAgent);


//-----------------------------------------------------------------------------
// Construction and setup
//-----------------------------------------------------------------------------

// Constructor
// Default values match GDB characteristics
GDBAgent::GDBAgent (XtAppContext app_context,
		    const string& gdb_call,
		    DebuggerType tp,
		    unsigned int nTypes)
    : TTYAgent (app_context, gdb_call, nTypes),
      state(BusyOnInitialCmds),
      _type(tp),
      _user_data(0),
      _has_frame_command(true),
      _has_func_command(false),
      _has_file_command(false),
      _has_run_io_command(false),
      _has_print_r_option(false),
      _has_output_command(false),
      _has_where_h_option(false),
      _has_display_command(true),
      _has_clear_command(true),
      _has_handler_command(false),
      _has_pwd_command(true),
      _has_setenv_command(false),
      _has_edit_command(false),
      _has_make_command(true),
      _has_jump_command(true),
      _has_regs_command(true),
      _has_watch_command(0),
      _has_named_values(true),
      _has_when_command(false),
      _has_when_semicolon(false),
      _wants_delete_comma(false),
      _has_err_redirection(true),
      _has_givenfile_command(false),
      _has_cont_sig_command(false),
      _has_examine_command(true),
      _has_rerun_command(false),
      _rerun_clears_args(false),
      _has_attach_command(true),
      _has_addproc_command(false),
      _has_debug_command(true),
      _is_windriver_gdb(false),
      _has_unwatch_command(false),
      _program_language(LANGUAGE_C),
      _verbatim(false),
      _recording(false),
      _detect_echos(true),
      _buffer_gdb_output(false),
      _flush_next_output(false),
      last_prompt(""),
      last_written(""),
      _title("DEBUGGER"),
      echoed_characters(-1),
      exception_state(false),
      questions_waiting(false),
      _qu_data(0),
      qu_index(0),
      _qu_count(0),
      cmd_array(0),
      complete_answers(0),
      _qu_datas(0),
      _qa_data(0),
      _on_answer(0),
      _on_answer_completion(0),
      _on_qu_array_completion(0),
      complete_answer("")
{
    // Suppress default error handlers
    removeAllHandlers(Panic);
    removeAllHandlers(Strange);
    removeAllHandlers(Died);

    // Add own handlers
    addHandler(Panic,   PanicHP);
    addHandler(Strange, StrangeHP);
    addHandler(Died,    DiedHP);
    addHandler(Input,   InputHP);

    // Add trace handlers
    addHandler(Input,  traceInputHP);     // GDB => DDD
    addHandler(Output, traceOutputHP);    // DDD => GDB
    addHandler(Error,  traceErrorHP);     // GDB Errors => DDD

    cpu = cpu_unknown;
}


// Copy constructor
GDBAgent::GDBAgent(const GDBAgent& gdb)
    : TTYAgent(gdb),
      state(gdb.state),
      _type(gdb.type()),
      _user_data(0),
      _has_frame_command(gdb.has_frame_command()),
      _has_func_command(gdb.has_func_command()),
      _has_file_command(gdb.has_file_command()),
      _has_run_io_command(gdb.has_run_io_command()),
      _has_print_r_option(gdb.has_print_r_option()),
      _has_output_command(gdb.has_output_command()),
      _has_where_h_option(gdb.has_where_h_option()),
      _has_display_command(gdb.has_display_command()),
      _has_clear_command(gdb.has_clear_command()),
      _has_handler_command(gdb.has_handler_command()),
      _has_pwd_command(gdb.has_pwd_command()),
      _has_setenv_command(gdb.has_setenv_command()),
      _has_edit_command(gdb.has_edit_command()),
      _has_make_command(gdb.has_make_command()),
      _has_jump_command(gdb.has_jump_command()),
      _has_regs_command(gdb.has_regs_command()),
      _has_watch_command(gdb.has_watch_command()),
      _has_named_values(gdb.has_named_values()),
      _has_when_command(gdb.has_when_command()),
      _has_when_semicolon(gdb.has_when_semicolon()),
      _wants_delete_comma(gdb.wants_delete_comma()),
      _has_err_redirection(gdb.has_err_redirection()),
      _has_givenfile_command(gdb.has_givenfile_command()),
      _has_cont_sig_command(gdb.has_cont_sig_command()),
      _has_examine_command(gdb.has_examine_command()),
      _has_rerun_command(gdb.has_rerun_command()),
      _rerun_clears_args(gdb.rerun_clears_args()),
      _has_attach_command(gdb.has_attach_command()),
      _has_addproc_command(gdb.has_addproc_command()),
      _has_debug_command(gdb.has_debug_command()),
      _is_windriver_gdb(gdb.is_windriver_gdb()),
      _program_language(gdb.program_language()),
      _verbatim(gdb.verbatim()),
      _recording(gdb.recording()),
      _detect_echos(gdb.detect_echos()),
      _buffer_gdb_output(gdb.buffer_gdb_output()),
      _flush_next_output(gdb.flush_next_output()),
      last_prompt(""),
      last_written(""),
      _title(""),
      echoed_characters(-1),
      exception_state(false),
      questions_waiting(false),
      _qu_data(0),
      qu_index(0),
      _qu_count(0),
      cmd_array(0),
      complete_answers(0),
      _qu_datas(0),
      _qa_data(0),
      _on_answer(0),
      _on_answer_completion(0),
      _on_qu_array_completion(0),
      complete_answer("")
{}

// Create GDBAgent matching type (Factory pattern)
GDBAgent*
GDBAgent::Create (XtAppContext app_context,
	      const string& gdb_call,
	      DebuggerType type)
{
    switch (type)
    {
	case BASH:
	    return (GDBAgent *) new GDBAgent_BASH (app_context, gdb_call); break;
	case DBG:
	    return (GDBAgent *) new GDBAgent_DBG (app_context, gdb_call); break;
	case DBX:
	    return (GDBAgent *) new GDBAgent_DBX (app_context, gdb_call); break;
	case GDB:
	    return (GDBAgent *) new GDBAgent_GDB (app_context, gdb_call); break;
	case JDB:
	    return (GDBAgent *) new GDBAgent_JDB (app_context, gdb_call); break;
	case PERL:
	    return (GDBAgent *) new GDBAgent_PERL (app_context, gdb_call); break;
	case PYDB:
	    return (GDBAgent *) new GDBAgent_PYDB (app_context, gdb_call); break;
	case XDB:
	    return (GDBAgent *) new GDBAgent_XDB (app_context, gdb_call); break;
	case MAKE:
	    return (GDBAgent *) new GDBAgent_MAKE (app_context, gdb_call); break;
	default:
	    assert (0);
    }
}

// Trace communication
void GDBAgent::trace(const char *prefix, void *call_data) const
{
    DataLength* dl    = (DataLength *) call_data;
    string s(dl->data, dl->length);

    bool s_ends_with_nl = false;
    if (s.length() > 0 && s[s.length() - 1] == '\n')
    {
	s_ends_with_nl = true;
	s = s.before(int(s.length() - 1));
    }

    s = quote(s);
    string nl = "\\n\"\n";
    nl += replicate(' ', strlen(prefix));
    nl += "\"";
    s.gsub("\\n", nl);

    if (s_ends_with_nl)
	s = s.before(int(s.length() - 1)) + "\\n" + 
	    s.from(int(s.length() - 1));


#if HAVE_STRFTIME
    char ltime[24];

    time_t t = time(NULL);
    struct tm tm = *localtime(&t);
    size_t r = strftime(ltime, sizeof(ltime), "%Y.%m.%d %H:%M:%S", &tm);
    ltime[r] = '\0';
#elif HAVE_ASCTIME
    time_t t = time(NULL);
    const char* ltime = asctime(localtime(&t));
#else
    const char* ltime = "";
#endif

    dddlog << ltime << (strlen(ltime)!=0 ?"\n":"") << prefix << s << '\n';
    dddlog.flush();
}
    
void GDBAgent::traceInputHP(Agent *source, void *, void *call_data)
{
    GDBAgent *gdb = ptr_cast(GDBAgent, source);
    if (gdb != 0)
	gdb->trace("<- ", call_data);
}

void GDBAgent::traceOutputHP(Agent *source, void *, void *call_data)
{
    GDBAgent *gdb = ptr_cast(GDBAgent, source);
    if (gdb != 0)
	gdb->trace("-> ", call_data);
}

void GDBAgent::traceErrorHP(Agent *source, void *, void *call_data)
{
    GDBAgent *gdb = ptr_cast(GDBAgent, source);
    if (gdb != 0)
	gdb->trace("<= ", call_data);
}

// Start GDBAgent
void GDBAgent::do_start (OAProc  on_answer,
			 OACProc on_answer_completion,
			 void*   user_data)
{
    _on_answer = on_answer;
    _on_answer_completion = on_answer_completion;
    _user_data = user_data;
    TTYAgent::start();
    callHandlers(ReadyForQuestion, (void *)false);
    callHandlers(ReadyForCmd, (void *)false);
    callHandlers(LanguageChanged, (void *)this);
}

// Start with some extra commands
void GDBAgent::start_plus (OAProc   on_answer,
			   OACProc  on_answer_completion,
			   void*    user_data,
			   const std::vector<string>& cmds,
			   const VoidArray& qu_datas,
			   int      qu_count,
			   OQACProc on_qu_array_completion,
			   void*    qa_data,
			   bool&    qa_data_registered)
{
    qa_data_registered = false;
    state = BusyOnInitialCmds;

    if (qu_count > 0) {
	questions_waiting = true;
	init_qu_array(cmds, qu_datas, qu_count, 
		      on_qu_array_completion, qa_data);
	qa_data_registered = true;
    }

    do_start(on_answer, on_answer_completion, user_data);
}

// Destructor
GDBAgent::~GDBAgent ()
{
    shutdown();
}



//-----------------------------------------------------------------------------
// Command sending
//-----------------------------------------------------------------------------

// Send CMD to GDB, associated with USER_DATA.  Return false iff busy.
bool GDBAgent::send_user_cmd(string cmd, void *user_data)  // without '\n'
{
    if (user_data)
	_user_data = user_data;

    switch (state) {
    case ReadyWithPrompt:
    case BusyOnInitialCmds:

	// Process CMD
	state = BusyOnCmd;
	complete_answer = "";
	callHandlers(ReadyForQuestion, (void *)false);
	cmd += '\n';
	write_cmd(cmd);
	flush();

	return true;

    case BusyOnQuArray:
    case BusyOnCmd:
	break;
    }

    return false;
}

// Send CMD to GDB (unconditionally), associated with USER_DATA.
bool GDBAgent::send_user_ctrl_cmd(const string& cmd, void *user_data)
{
    if (user_data)
	_user_data = user_data;

    // Upon ^D, GDB is no more in state to receive commands.
    // Expect a new prompt to appear.
    if (cmd == '\004' && state == ReadyWithPrompt)
    {
	state = BusyOnCmd;
	complete_answer = "";
    }

    write(cmd);
    flush();
    return true;
}

// Send command array CMDS to GDB, associated with QU_DATAS.
bool GDBAgent::send_user_cmd_plus (const std::vector<string>& cmds,
				   const VoidArray& qu_datas,
				   int      qu_count,
				   OQACProc on_qu_array_completion,
				   void*    qa_data,
				   bool& qa_data_registered,
				   string   user_cmd,
				   void* user_data)
{
    qa_data_registered = false;
    if (state != ReadyWithPrompt) 
	return false;

    if (user_data)
	_user_data = user_data;
    if (qu_count > 0)
    {
	questions_waiting = true;
	init_qu_array(cmds, qu_datas, qu_count,
		      on_qu_array_completion, qa_data);
	qa_data_registered = true;
    }

    // Process command
    state = BusyOnCmd;
    complete_answer = "";
    callHandlers(ReadyForQuestion, (void *)false);
    user_cmd += '\n';
    write_cmd(user_cmd);
    flush();

    return true;
}

// Send CMDS to GDB; upon completion, call ON_QU_ARRAY_COMPLETION with QU_DATAS
bool GDBAgent::send_qu_array (const std::vector<string>& cmds,
			      const VoidArray& qu_datas,
			      int      qu_count,
			      OQACProc on_qu_array_completion,
			      void*    qa_data,
			      bool& qa_data_registered)
{
    qa_data_registered = false;
    if (qu_count == 0)
	return true;
    if (state != ReadyWithPrompt)
	return false;

    state = BusyOnQuArray;
    callHandlers(ReadyForQuestion, (void *)false);
    callHandlers(ReadyForCmd, (void *)false);

    init_qu_array(cmds, qu_datas, qu_count, on_qu_array_completion, qa_data);
    qa_data_registered = true;

    // Send first question
    write_cmd(cmd_array[0]);
    flush();

    return true;
}

// Initialize GDB question array
void GDBAgent::init_qu_array (const std::vector<string>& cmds,
			      const VoidArray& qu_datas,
			      int      qu_count,
			      OQACProc on_qu_array_completion,
			      void*    qa_data)
{
    _on_qu_array_completion = on_qu_array_completion;
    qu_index  = 0;
    _qu_count = qu_count;
    _qa_data  = qa_data;

    static const std::vector<string> empty_s;
    static const VoidArray   empty_v;

    complete_answers = empty_s;
    cmd_array        = empty_s;
    _qu_datas        = empty_v;
    for (int i = 0; i < qu_count; i++)
    {
	complete_answers.push_back("");
	cmd_array.push_back(cmds[i] + '\n');
	_qu_datas.push_back(qu_datas[i]);
    }
}


//-----------------------------------------------------------------------------
// Prompt Recognition
//-----------------------------------------------------------------------------

// Return true iff ANSWER ends with primary prompt.
bool GDBAgent::ends_with_prompt (const string& ans)
{
    /* UNUSED */ (void (ans));
    assert(0);
}

static bool ends_in(const string& answer, const char *prompt)
{
    return answer.contains(prompt, answer.length() - strlen(prompt));
}

void GDBAgent::set_exception_state(bool new_state)
{
    if (new_state != exception_state)
    {
	exception_state = new_state;
	callHandlers(ExceptionState, (void *)exception_state);

	if (exception_state && state != ReadyWithPrompt)
	{
	    // Report the exception message like an unexpected output
	    callHandlers(AsyncAnswer, (void *)&complete_answer);
	}
    }
}

// Return true iff ANSWER ends with (yes or no)
bool GDBAgent::ends_with_yn (const string& answer) const
{
    if (ends_in(answer, "(y or n) "))
	return true;		// GDB

    if (ends_in(answer, "(y or [n]) "))
	return true;		// GDB

    if (ends_in(answer, "(y/n): "))
	return true;		// BASH

    if (ends_in(answer, "(yes or no) "))
	return true;

    if ((type() == XDB || type() == JDB) && ends_in(answer, "? "))
	return true;

    return false;
}


// Check if ANSWER requires an immediate reply; return it.
string GDBAgent::requires_reply (const string& answer)
{
    // GDB says: `---Type <return> to continue, or q <return> to quit---'
    // DBX 3.0 says: `line N', `(END)', `(press RETURN)', and `More (n if no)?'
    // XDB says: `--More--' and `Hit RETURN to continue'.
    // Escape sequences may also be embedded, but the prompt never
    // ends in a newline.

    if (answer.contains('\n', -1) || ends_with_prompt(answer))
	return "";
    int last_line_index = answer.index('\n', -1) + 1;

    string last_line = answer.chars() + last_line_index;
    last_line.downcase();
    strip_control(last_line);

    if (last_line.contains("end") 
	|| last_line.contains("line")
	|| last_line.contains("more")
	|| last_line.contains("cont:")
	|| last_line.contains("return"))
    {
#if RUNTIME_REGEX
	static regex rxq(".*[(]END[)][^\n]*");
#endif
	if (answer.matches(rxq, last_line_index))
	    return "q";		// Stop this

#if RUNTIME_REGEX
	static regex rxspace(".*(--More--|line [0-9])[^\n]*");
#endif
	if (answer.matches(rxspace, last_line_index))
	    return " ";		// Keep on scrolling

#if RUNTIME_REGEX
	static regex rxreturn(".*([(]press RETURN[)]"
			      "|Hit RETURN to continue"
			      "|Type <return> to continue"
			      "|  cont: "
			      "|More [(]n if no[)][?])[^\n]*");
#endif
	if (answer.matches(rxreturn, last_line_index))
	    return "\n";		// Keep on scrolling

	if (type() == XDB)
	{
	    // Added regular expression for "Standard input: END" to
	    // GDBAgent::requires_reply 
	    // -- wiegand@kong.gsfc.nasa.gov (Robert Wiegand)
#if RUNTIME_REGEX
	    static regex rxxdb(".*Standard input: END.*");
#endif
	    if (answer.matches(rxxdb, last_line_index))
		return "\n";	// Keep on scrolling
	}
    }

    return "";
}



//-----------------------------------------------------------------------------
// Filters
//-----------------------------------------------------------------------------

// Normalize answer - handle control characters, remove comments and prompt
void GDBAgent::normalize_answer(string& answer) const
{
    strip_control(answer);
    strip_dbx_comments(answer);
    cut_off_prompt(answer);
}

// Strip annoying DBX comments
void GDBAgent::strip_dbx_comments(string& s) const
{
    if (type() == DBX)
    {
	// Weed out annoying DBX warnings like
	// `WARNING: terminal cannot clear to end of line'
	for (;;)
	{
	    int warning = s.index("WARNING: terminal cannot ");
	    if (warning < 0)
		break;
	    int eol = s.index('\n', warning) + 1;
	    if (eol <= 0)
		eol = s.length();
	    s.at(warning, eol - warning) = "";
	}
    }

    // If we're verbatim, leave output unchanged.
    if (verbatim())
	return;

    // All remaining problems occur in Sun DBX 3.x only.
    if (!has_print_r_option())
	return;

    if (s.contains('/'))
    {
	// Check for C and C++ comments
	char quoted = '\0';

	unsigned int i = 0;
	while (i < s.length())
	{
	    char c = s[i++];
	    switch (c)
	    {
	    case '\\':
		if (i < s.length())
		    i++;
		break;

	    case '\'':
	    case '\"':
		if (c == quoted)
		    quoted = '\0';
		else if (!quoted)
		    quoted = c;
		break;

	    case '/':
		if (i < s.length() && !quoted)
		{
		    if (s[i] == '*')
		    {
			/* C-style comment */
			int end = s.index("*/", i + 1);
			if (end == -1)
			{
			    // unterminated comment -- keep it now
			    break;
			}

			// Remove comment
			i--;
			s.at(int(i), int(end - i + 2)) = "";
		    }
		    else if (s[i] == '/')
		    {
			// C++-style comment
			int end = s.index('\n', i + 1);
			i--;

			// Remove comment
			if (end == -1)
			    s.from(int(i)) = "";
			else
			    s.at(int(i), int(end - i)) = "";
		    }
		}
	    }
	}
    }

    if (s.contains("dbx: warning:"))
    {
	// Weed out annoying DBX warnings like
	// `dbx: warning: -r option only recognized for C++' and
	// `dbx: warning: unknown language, 'c' assumed'

#if RUNTIME_REGEX
	static regex rxdbxwarn1("dbx: warning:[^\n]*"
				"option only recognized for[^\n]*\n");
	static regex rxdbxwarn2("dbx: warning:[^\n]*"
				"unknown language[^\n]*\n");
#endif
	s.gsub(rxdbxwarn1, "");
	s.gsub(rxdbxwarn2, "");
    }
}

// Strip control characters
void GDBAgent::strip_control(string& answer) const
{
    int source_index = 0;
    int target_index = 0;

    for (source_index = 0; source_index < int(answer.length()); source_index++)
    {
	char c = answer[source_index];
	switch (c)
	{
	case '\b':
	    // Delete last character
	    if (target_index > 0 && answer[target_index - 1] != '\n')
		target_index--;
	    else
	    {
		// Nothing to erase -- keep the '\b'.
		goto copy;
	    }
	    break;

	case '\r':
	    if (source_index + 1 < int(answer.length()))
	    {
		if (answer[source_index + 1] == '\n' ||
		    answer[source_index + 1] == '\r')
		{
		    // '\r' followed by '\n' or '\r' -- don't copy
		    break;
		}
	        else
		{
		    // '\r' followed by something else: 
		    // Return to beginning of line
		    while (target_index > 0 && 
			   answer[target_index - 1] != '\n')
			target_index--;
		}
	    }
	    else
	    {
		// Trailing '\r' -- keep it
		goto copy;
	    }
	    break;

	case '\032':
	    // In annotation level 1, GDB sends out `annotation'
	    // sequences like `\n\032\032prompt\n' or `\032\032prompt\n'.
	    // We use some of these to find the current source position.
	    if (
		  (
		    ( // if we've just seen a newline
		 	target_index > 0 && answer[target_index - 1] == '\n'
		    )
		    ||   // or if this is the start of the line
		    target_index == 0
		  )
		  &&    // and the next character's also a Ctrl-Z
		  source_index + 1 < int(answer.length()) &&
		  answer[source_index + 1] == '\032'
	        )
	    {
		// Ignore everything up to and including the next '\n'.
		int i = source_index;
		while (i < int(answer.length()) &&
		       answer[i] != '\n' && answer[i] != ':')
		    i++;
		if (i >= int(answer.length()))
		{
		    // The annotation is not finished yet -- copy it
		    goto copy;
		}
		else if (answer[i] == ':')
		{
		    // This is a normal `fullname' annotation, handled by DDD
		    goto copy;
		}
		else
		{
		    // Annotation found -- ignore it
		    if (target_index > 0)
		    {
			assert(answer[target_index - 1] == '\n');
			target_index--;
			assert(answer[i] == '\n');
		    }
		    source_index = i;
		}
	    }
	    else
	    {
		// Single or trailing `\032' -- keep it
		goto copy;
	    }
	    break;

	case '\033':		// aka `\e'
	    // XDB `more' and Ladebug send VT100 escape sequences like `\e[m',
	    // `\e[22;1H', `\e[7m', `\e[K', regardless of TERM
	    // settings.  We simply weed out everything up to and
	    // including to the next letter.
	    while (source_index < int(answer.length()) && 
		   !isalpha(answer[source_index]))
		source_index++;

	    if (source_index >= int(answer.length()))
	    {
		// The escape sequence is not finished yet - keep the '\e'.
		answer[target_index++] = c;
	    }
	    break;

	copy:
	default:
	    // Leave character unchanged
	    answer[target_index++] = answer[source_index];
	    break;
	}
    }

    answer = answer.before(target_index);
}


//-----------------------------------------------------------------------------
// Event handlers
//-----------------------------------------------------------------------------

// Received data from GDB

void GDBAgent::InputHP(Agent *agent, void *, void *call_data)
{
    GDBAgent* gdb = ptr_cast(GDBAgent, agent);
    assert(gdb != 0);

    DataLength* dl = (DataLength *) call_data;
    string answer(dl->data, dl->length);

    gdb->handle_input(answer);
}

void GDBAgent::handle_echo(string& answer)
{
    // If we don't detect echos, leave output unchanged.
    if (!detect_echos())
	return;

    // Check for echoed characters.  Every now and then, the TTY setup
    // fails such that we get characters echoed back.  This may also
    // happen with remote connections.
    if (echoed_characters >= 0)
    {
	int i = 0;
	int e = echoed_characters;
	while (i < int(answer.length()) && e < int(last_written.length()))
	{
	    if (answer[i] == '\r')
	    {
		// Ignore '\r' in comparisons
		i++;
	    }
	    else if (answer[i] == last_written[e])
	    {
		i++, e++;
	    }
	    else
	    {
		// No echo
		break;
	    }
	}

	if (e >= int(last_written.length()))
	{
	    // All characters written have been echoed.
	    // Remove echoed characters and keep on processing.
	    callHandlers(EchoDetected, (void *)true);
	    answer = answer.from(i);
	    echoed_characters = -1;
	}
	else if (i >= int(answer.length()))
	{
	    // A prefix of the last characters written has been echoed.
	    // Wait for further echos.
	    answer = "";
	    echoed_characters = e;
	}
	else
	{
	    // No echo.
	    // => Restore any echoed characters and keep on processing
	    answer.prepend(last_written.before(echoed_characters));
	    echoed_characters = -1;

	    // If a command of length ECHO_THRESHOLD is not echoed,
	    // disable echo detection.  The idea behind this is that
	    // echo disabling seems to have succeeded and we thus no
	    // longer need to check for echos.  This reduces the risk
	    // of echo detection altering output data.

	    // ECHO_THRESHOLD is 4 because the inferior debugger might
	    // not echo short interludes like `yes\n', `no\n' or `^C'.
	    const unsigned int ECHO_THRESHOLD = 4;

	    if (last_written.length() > ECHO_THRESHOLD)
	    {
		// No more echos - disable echo detection until re-activated
		callHandlers(EchoDetected, (void *)false);
		detect_echos(false);
	    }
	}
    }
}

void GDBAgent::handle_more(string& answer)
{
    // Check for `More' prompt
    string reply = requires_reply(answer);
    if (!reply.empty())
    {
	// Oops - this should not happen.  Just hit the reply key.
	write(reply);
	flush();

	// Ignore the last line (containing the `More' prompt)
	const int last_beginning_of_line = answer.index('\n', -1) + 1;
	answer.from(last_beginning_of_line) = "";
    }
}

void GDBAgent::handle_reply(string& answer)
{
    if (recording())
	return;

    // Check for secondary prompt
    if (ends_with_secondary_prompt(answer))
    {
	// GDB requires more information here: probably the
	// selection of an ambiguous C++ name.
	// We simply try the first alternative here:
	// - in GDB, this means `all';
	// - in DBX and XDB, this is a non-deterministic selection.

	ReplyRequiredInfo info;
	info.question = answer;
	info.reply = "1\n";

	// Allow handlers to override the default reply
	callHandlers(ReplyRequired, (void *)&info);

	// Send reply immediately
	write(info.reply);
	flush();

	// Ignore the selection
	answer = info.question;
    }

    // Check for `yes or no'
    if (state != BusyOnCmd && ends_with_yn(answer))
    {
	ReplyRequiredInfo info;
	info.question = answer;
	info.reply = "no\n";

	// Allow handlers to override the default reply
	callHandlers(YesNoRequired, (void *)&info);

	// Send reply immediately
	write(info.reply);
	flush();

	// Ignore the selection
	answer = info.question;
    }
}

bool GDBAgent::recording(bool val)
{
    if (_recording != val)
    {
	_recording = val;
	callHandlers(Recording, (void *)recording());
    }
    return recording();
}

void GDBAgent::handle_input(string& answer)
{
    bool had_a_prompt;

    OAProc  on_answer = _on_answer;
    OACProc on_answer_completion = _on_answer_completion;
    void *user_data = _user_data;

    handle_echo(answer);
    handle_more(answer);
    handle_reply(answer);

    if (exception_state && state != ReadyWithPrompt)
    {
	// Be sure to report the exception like an unexpected output
	callHandlers(AsyncAnswer, (void *)&answer);
    }

    // Handle all other GDB output, depending on current state.
    switch (state)
    {
    case ReadyWithPrompt:
	// We have a prompt, and still get input?  Maybe this is an
	// answer to a command sent before the prompt was received -
	// or a reply to a control character (`Quit').
	strip_control(answer);
	callHandlers(AsyncAnswer, (void *)&answer);

	// Save answer in case of exceptions.
	complete_answer += answer;
	if (ends_with_prompt(complete_answer))
	{
	    set_exception_state(false);
	    complete_answer = "";
	}
	break;

    case BusyOnInitialCmds:
    case BusyOnCmd:
	complete_answer += answer;

	had_a_prompt = ends_with_prompt(complete_answer);

	if (had_a_prompt)
	    set_exception_state(false);

	if (_on_answer != 0)
	{
	    bool ready_to_process = true;

	    if (buffer_gdb_output())
	    {
		// Buffer answer
		ready_to_process = 
		    had_a_prompt || ends_with_yn(complete_answer);

		if (flush_next_output() && !ready_to_process)
		{
		    // Flush this answer
		    flush_next_output(false);
		    ready_to_process = true;

		    // Don't include it in the complete answer
		    complete_answer = 
			complete_answer.before(int(complete_answer.length() - 
						   answer.length()));
		}
		else
		{
		    // Simply buffer it all until we're ready.
		    if (ready_to_process)
			answer = complete_answer;
		}
	    }

	    if (ready_to_process)
	    {
		// Handle now
		if (had_a_prompt)
		{
		    normalize_answer(answer);
		}
		else
		{
		    strip_control(answer);
		    strip_dbx_comments(answer);
		}
		
		on_answer(answer, user_data);
	    }
	}

	if (had_a_prompt)
	{
            // Received complete answer (GDB issued prompt)

            // Set new state and call answer procedure
	    if (state == BusyOnInitialCmds)
	    {
		if (!questions_waiting) 
		{
		    state = ReadyWithPrompt;
		    callHandlers(ReadyForCmd, (void *)true);
		    callHandlers(ReadyForQuestion, (void *)true);

		    if (on_answer_completion != 0)
			on_answer_completion(user_data);
		}
		else
		{
		    state = BusyOnQuArray;

		    // Send first question
		    write_cmd(cmd_array[0]);
		    flush();
		}
	    }
	    else if (!questions_waiting)
	    {
		state = ReadyWithPrompt;
		callHandlers(ReadyForQuestion, (void *)true);

		if (on_answer_completion != 0)
		    on_answer_completion(user_data);
	    }
	    else
	    {
		state = BusyOnQuArray;
		callHandlers(ReadyForCmd, (void *)false);

		// Send first question
		write_cmd(cmd_array[0]);
		flush();
	    }
	}
	break;

    case BusyOnQuArray:
	complete_answers[qu_index] += answer;

	if (ends_with_prompt(complete_answers[qu_index]))
	{
	    set_exception_state(false);

            // Answer is complete (GDB issued prompt)
	    normalize_answer(complete_answers[qu_index]);

	    if (qu_index == _qu_count - 1)
	    {
		// Received all answers -- we're ready again
		state = ReadyWithPrompt;
		callHandlers(ReadyForQuestion, (void *)true);
		callHandlers(ReadyForCmd, (void *)true);

		if (questions_waiting || _on_qu_array_completion != 0)
		{
		    // We use a local copy of the answers and user
		    // data here, since the callback may submit a new
		    // query, overriding the original value.
		    std::vector<string> answers(complete_answers);
		    VoidArray datas(_qu_datas);
		    OQACProc array_completion  = _on_qu_array_completion;
		    OACProc  answer_completion = _on_answer_completion;
		    void *array_data           = _qa_data;

		    if (questions_waiting)
		    {
			// We did not call the OACProc yet.
			questions_waiting = false;

			if (answer_completion != 0)
			    answer_completion(_user_data);
		    }
		    if (array_completion != 0)
			array_completion(answers, datas, array_data);
		}
	    }
	    else
	    {
		// Send next question
		write_cmd(cmd_array[++qu_index]);
		flush();
	    }
	}
	break;

    default:
	assert(0);
	::abort();
	break;
    }

    if (is_exception_answer(complete_answer))
	set_exception_state(true);
}

// Write arbitrary data
int GDBAgent::write(const char *data, int length)
{
    last_written = string(data, length);

    echoed_characters = 0;
    return TTYAgent::write(data, length);
}

// GDB died
void GDBAgent::DiedHP(Agent *agent, void *, void *)
{
    GDBAgent *gdb = ptr_cast(GDBAgent, agent);
    gdb->handle_died();
}

void GDBAgent::handle_died()
{
    // We have no prompt
    last_prompt = "";

    // Call answer completion handlers
    switch (state)
    {
    case ReadyWithPrompt:
	break;

    case BusyOnInitialCmds:
    case BusyOnCmd:
	if (_on_answer_completion != 0)
	    _on_answer_completion (_user_data);
	break;

    case BusyOnQuArray:
	if (_on_qu_array_completion != 0)
	    _on_qu_array_completion(complete_answers, _qu_datas, _qa_data);
	break;
    }

    // We're not ready anymore
    state = BusyOnCmd;
    complete_answer = "";
    callHandlers(ReadyForQuestion, (void *)false);
    callHandlers(ReadyForCmd,      (void *)false);
}


//-----------------------------------------------------------------------------
// Configuration
//-----------------------------------------------------------------------------

// DBX 3.0 wants `display -r' instead of `display' for C++
string GDBAgent::display_command(const char *expr) const
{
    string cmd;
    if (!has_display_command())
	return cmd;

    if (has_print_r_option() && strlen(expr) != 0)
	cmd = "display -r";
    else
	cmd = "display";

    if (strlen(expr) != 0) {
        cmd += ' ';
        cmd += expr;
    }

    return cmd;
}

string GDBAgent::where_command(int count) const
{
    string cmd;

    if (has_where_h_option())
	cmd = "where -h";
    else
	cmd = "where";

    if (count != 0)
	cmd += " " + itostring(count);

    return cmd;
}

// Some DBXes want `sh pwd' instead of `pwd'
string GDBAgent::pwd_command() const
{
    if (has_pwd_command())
	return "pwd";
    else
	return "sh pwd";
}



string GDBAgent::frame_command() const
{
    if (has_frame_command())
	return "frame";
    else
	return where_command(1);
}

string GDBAgent::frame_command(int num) const
{
    return frame_command() + " " + itostring(num);
}

// Add OFFSET to current frame (i.e. OFFSET > 0: up, OFFSET < 0: down)
string GDBAgent::relative_frame_command(int offset) const
{
    if (offset == -1)
	return "down";
    else if (offset < 0)
	return "down " + itostring(-offset);
    else if (offset == 1)
	return "up";
    else if (offset > 0)
	return "up " + itostring(offset);

    return "";			// Offset == 0
}

// Each debugger has its own way of echoing (sigh)
string GDBAgent::echo_command(const string& text) const
{
    return "echo " + cook(text);
}

// Return actual debugger command, with args
string GDBAgent::cmd() const
{
    string cmd = path();

    for (;;)
    {
	// We might get called as `/bin/sh -c 'exec CMD ARGS''.  Handle this.
	strip_leading_space(cmd);
	if (cmd.contains("/bin/sh -c ", 0))
	{
	    cmd = cmd.after("-c ");
	    strip_leading_space(cmd);
	    if (cmd.contains('\'', 0) || cmd.contains('\"', 0))
	    {
		cmd.gsub("\'\\\'\'", '\'');
		cmd = unquote(cmd);
	    }
	}
	else if (cmd.contains("exec ", 0))
	{
	    cmd = cmd.after("exec ");
	}
	else
	{
	    break;
	}
    }

    strip_space(cmd);
    return cmd;
}

// Return name of debugger
string GDBAgent::debugger() const
{
    string debugger = cmd();
    if (debugger.contains(' '))
	debugger = debugger.before(' ');

    if (debugger.contains('\'', 0) || debugger.contains('\"', 0))
	debugger = unquote(debugger);

    strip_space(debugger);
    return debugger;
}

// Return debugger arguments (including program name)
string GDBAgent::args() const
{
    string args = cmd();

    args = args.after(' ');
    strip_leading_space(args);

    if (args.contains('\'', 0) || args.contains('\"', 0))
	args = unquote(args);

    strip_space(args);
    return args;
}

// Return debugged program
string GDBAgent::program() const
{
    string program = args();
    while (program.contains("-", 0))
    {
	// Skip options
	program = program.after(' ');
	strip_leading_space(program);
    }

    if (program.contains(' '))
	program = program.before(' ');
    if (program.contains('\'', 0) || program.contains('\"', 0))
	program = unquote(program);

    return program;
}

// Place quotes around filename FILE if needed
string GDBAgent::quote_file(const string& file) const
{
    if (type() == GDB && file.contains(rxwhite))
    {
	// GDB has no special processing for characters within quotes
	// (i.e. backslashes, etc.)
	return '\'' + file + '\'';
    }
    else
    {
	return file;
    }
}

// Return a command that does nothing.
string GDBAgent::nop_command(const char *comment) const
{
    if (type() == JDB)
	return " ";

    return string("# ") + comment;	// Works for all other inferior debuggers
}

// Return PREFIX + EXPR, parenthesizing EXPR if needed
string GDBAgent::prepend_prefix(const string& prefix, const string& expr)
{
  return prepend_prefix( prefix.chars(), expr);
}

string GDBAgent::prepend_prefix(const char *prefix, const string& expr)
{
    if (expr.matches(rxidentifier)
	|| (expr.contains("(", 0) && expr.contains(")", -1)))
	return prefix + expr;
    else if (expr.empty())
	return prefix;
    else
	return string(prefix) + "(" + expr + ")";
}

// Return EXPR + SUFFIX, parenthesizing EXPR if needed
string GDBAgent::append_suffix(const string& expr, const string &suffix)
{
  return append_suffix( expr, suffix.chars() );
}

string GDBAgent::append_suffix(const string& expr, const char *suffix)
{
    if (expr.matches(rxidentifier)
	|| (expr.contains("(", 0) && expr.contains(")", -1)))
	return expr + suffix;
    else if (expr.empty())
	return string(suffix);
    else
	return "(" + expr + ")" + suffix;
}

// Dereference an expression.
string GDBAgent::dereferenced_expr(const string& expr) const
{
    switch (program_language())
    {
    case LANGUAGE_C:
	return prepend_prefix("*", expr);

    case LANGUAGE_BASH:
    case LANGUAGE_MAKE:
    case LANGUAGE_PHP:
    case LANGUAGE_PERL:
	// Perl has three `dereferencing' operators, depending on the
	// type of reference.  The `deref()' function provides a
	// better solution.
	return prepend_prefix("$", expr);

    case LANGUAGE_FORTRAN:
	// GDB prints dereferenced pointers as `**X', but accepts them as `*X'.
	return prepend_prefix("*", expr);

    case LANGUAGE_JAVA:
	if (type() == GDB)
	{
	    // GDB dereferences JAVA references by prepending `*'
	    return prepend_prefix("*", expr);
	}

	// JDB (and others?) dereference automatically
	return expr;

    case LANGUAGE_CHILL:
	return append_suffix(expr, "->");

    case LANGUAGE_PASCAL:
	return append_suffix(expr, "^");

    case LANGUAGE_ADA:
	// GDB 4.16.gnat.1.13 prepends `*' as in C
	return prepend_prefix("*", expr);

    case LANGUAGE_PYTHON:
	return "";		// No such thing in Python/PYDB

    case LANGUAGE_OTHER:
	return expr;		// All other languages
    }

    return expr;		// All other languages
}

// Give the address of an expression.
string GDBAgent::address_expr(string expr) const
{
    if (expr.contains('/', 0))
	expr = expr.after(' ');

    switch (program_language())
    {
    case LANGUAGE_C:
	return prepend_prefix("&", expr);

    case LANGUAGE_PASCAL:
	return "ADR(" + expr + ")"; // Modula-2 address operator

    case LANGUAGE_CHILL:	// FIXME: untested.
	return prepend_prefix("->", expr);

    case LANGUAGE_FORTRAN:
	return prepend_prefix("&", expr);

    case LANGUAGE_JAVA:
	return "";		// Not supported in GDB

    case LANGUAGE_PYTHON:
	return "";		// Not supported in Python

    case LANGUAGE_BASH:
    case LANGUAGE_MAKE:
    case LANGUAGE_PHP:          // Is this right? 
    case LANGUAGE_PERL:
	return "";		// No such thing in bash/make/Perl

    case LANGUAGE_ADA:
	return "";		// Not supported in GNAT/Ada

    case LANGUAGE_OTHER:
	return "";		// All other languages
    }

    return "";			// All other languages
}

// Give the index of an expression.
string GDBAgent::index_expr(const string& expr, const string& index) const
{
    switch (program_language())
    {
    case LANGUAGE_FORTRAN:
    case LANGUAGE_ADA:
	return expr + "(" + index + ")";

    case LANGUAGE_PERL:
	if (!expr.empty() && expr[0] == '@')
	    return '$' + expr.after(0) + "[" + index + "]";
	else
	    return expr + "[" + index + "]";

    case LANGUAGE_BASH:
      return "${" + expr + "[" + index + "]}";

    // Not sure if this is really right.
    case LANGUAGE_MAKE:
      return "$(word $(" + expr + ")," + index + ")";

    default:
	break;
    }

    // All other languages
    return expr + "[" + index + "]";
}

// Return default index base
int GDBAgent::default_index_base() const
{
    switch (program_language())
    {
    case LANGUAGE_FORTRAN:
    case LANGUAGE_PASCAL:
    case LANGUAGE_CHILL:
	return 1;

    case LANGUAGE_ADA:
    case LANGUAGE_BASH:
    case LANGUAGE_C:
    case LANGUAGE_JAVA:
    case LANGUAGE_MAKE:
    case LANGUAGE_PERL:
    case LANGUAGE_PHP:
    case LANGUAGE_PYTHON:
    case LANGUAGE_OTHER:
	return 0;
    }

    return 0;			// Never reached
}

// Return member separator
string GDBAgent::member_separator() const
{
    switch (program_language())
    {
    case LANGUAGE_FORTRAN:
    case LANGUAGE_PASCAL:
    case LANGUAGE_CHILL:
    case LANGUAGE_C:
    case LANGUAGE_PYTHON:
    case LANGUAGE_OTHER:
    case LANGUAGE_PHP:
	return " = ";

    case LANGUAGE_JAVA:
	return ": ";

    case LANGUAGE_BASH:
    case LANGUAGE_MAKE:   // Might consider members of archives. Or target stem
        return "";

    case LANGUAGE_ADA:
    case LANGUAGE_PERL:
	return " => ";
    }

    return "";			// Never reached
}

void GDBAgent::normalize_address(string& addr) const
{
    // In C, hexadecimal integers are specified by a leading "0x".
    // In Modula-2, hexadecimal integers are specified by a trailing "H".
    // In Chill, hexadecimal integers are specified by a leading "H'".
    addr.downcase();
    if (addr.contains("0", 0))
	addr = addr.after("0");
    if (addr.contains("x", 0))
	addr = addr.after("x");
    if (addr.contains("h'", 0))
	addr = addr.after("h'");
    if (addr.contains("h", -1))
	addr = addr.before(int(addr.length()) - 1);

    if (!addr.empty())
    {
	switch (program_language())
	{
	case LANGUAGE_ADA:
	case LANGUAGE_BASH:
	case LANGUAGE_C:
	case LANGUAGE_FORTRAN:
	case LANGUAGE_JAVA:
	case LANGUAGE_MAKE:
	case LANGUAGE_PERL:
	case LANGUAGE_PHP:
	case LANGUAGE_PYTHON:
	case LANGUAGE_OTHER:
	    addr.prepend("0x");
	    break;

	case LANGUAGE_CHILL:
	    addr = "H'0" + upcase(addr);
	    break;

	case LANGUAGE_PASCAL:
	    addr = "0" + upcase(addr) + "H";
	    break;
	}
    }
}

// Return disassemble command
string GDBAgent::disassemble_command(string start, const char *end) const
{
    string cmd;
    if (type() != GDB)
	return cmd;

    normalize_address(start);
    cmd = "disassemble " + start;

    if (strlen(end) != 0)
    {
        string end_( end );
	normalize_address(end_);
	cmd += ", ";
	cmd += end_;
    }
    return cmd;
}

// Return true iff A contains the word S
static bool contains_word(const string& a, const string& s)
{
    int index = -1;
    for (;;)
    {
	index = a.index(s, index + 1);
	if (index < 0)
	    break;

	if (index > 0 && isalpha(a[index - 1]))
	    continue;		// Letter before S

	int next = index + s.length();
	if (next < int(a.length()) && isalpha(a[next]))
	    continue;		// Letter after S

	return true;		// Okay
    }

    return false;		// Not found
}

// Determine language from TEXT
ProgramLanguage GDBAgent::program_language(string text)
{
    text.downcase();

    if (type() == GDB && text.contains("language"))
	text = text.after("language");

    if (text.contains("\n"))
	text = text.before("\n");

    static struct {
	const char *name;
	ProgramLanguage language;
    } const language_table[] = {
	{ "ada",     LANGUAGE_ADA },
	{ "bash",    LANGUAGE_BASH },
	{ "c",       LANGUAGE_C },
	{ "c++",     LANGUAGE_C },
	{ "chill",   LANGUAGE_CHILL },
	{ "fortran", LANGUAGE_FORTRAN },
	{ "f",       LANGUAGE_FORTRAN }, // F77, F90, F
	{ "java",    LANGUAGE_JAVA },
	{ "make",    LANGUAGE_MAKE },
	{ "modula",  LANGUAGE_PASCAL },
	{ "m",       LANGUAGE_PASCAL }, // M2, M3 or likewise
	{ "pascal",  LANGUAGE_PASCAL },
	{ "perl",    LANGUAGE_PERL },
	{ "python",  LANGUAGE_PYTHON },
	{ "php",     LANGUAGE_PHP },
	{ "auto",    LANGUAGE_OTHER }  // Keep current language
    };

    for (int i = 0; 
	 i < int(sizeof(language_table) / sizeof(language_table[0])); i++)
    {
	if (contains_word(text, language_table[i].name))
	{
	    ProgramLanguage new_language = language_table[i].language;
	    if (new_language != LANGUAGE_OTHER)
		program_language(new_language);

	    return program_language();
	}
    }

    // Unknown language - switch to default setting
    program_language(LANGUAGE_C);
    return program_language();
}


//-----------------------------------------------------------------------------
// Perl specials
//-----------------------------------------------------------------------------

void GDBAgent::split_perl_var(const string& var,
			      string& prefix,
			      string& package,
			      string& name)
{
    name = var.from(rxalpha);
    if (name.empty())
	name = var.from("_");
    if (name.empty())
	return;
    prefix = var.before(name);

    package = "";
    if (name.contains("::"))
    {
	package = name.before("::", -1);
	name = name.after(package + "::");
    }
}

// Bring VALUE into a form that might be recognized by DDD
void GDBAgent::munch_perl_scalar(string& value)
{
    strip_leading_space(value);
    if (value.contains("0  ", 0))
	value = value.after("0");

    strip_leading_space(value);
#if RUNTIME_REGEX
#define RXADDRESS "(0x[0-9a-fA-F]+|0[0-9a-fA-F]+[hH]|H'[0-9a-fA-F]+" \
                  "|00+|[(]nil[)]|NIL|null|@[0-9a-fA-F]+|16_[0-9a-f]+)"
#define STANDARD_IDENTFIER "([A-Za-z_$@%][A-Za-z0-9_$]*|[$]([^ \n\t\f]|[0-9]+))"
        static regex rxperlref("((" STANDARD_IDENTFIER "::)*" STANDARD_IDENTFIER "=)?" STANDARD_IDENTFIER "[(]" RXADDRESS "[)]");
#endif
    if (value.contains(rxperlref, 0))
	value = value.before('\n');
}

// Bring VALUE into a form that might be recognized by DDD
void GDBAgent::munch_perl_array(string& value, bool hash)
{
    int n = value.freq('\n');
    string *lines = new string[n + 1];
    split(value, lines, n + 1, '\n');

    bool compact = false;
    bool first_elem = true;
    string new_value;
    bool arrow = true;

    for (int i = 0; i < n; i++)
    {
	string line = lines[i];
	if (!compact && line.contains(' ', 0))
	    continue;		// Sub-element; ignore line

	strip_space(line);

	if (!compact && line.contains(rxint, 0))
	{
	    // Strip index
	    line = line.after(rxint);

	    if (line.contains("..", 0))
	    {
		// In compact representation, Perl omits individual
		// indexes, and puts a START..END index instead.
		compact = true;
		line = line.after(rxint);
	    }
	    strip_space(line);
	}

	if (!first_elem)
	{
	    if (hash && arrow)
		new_value += " => ";
	    else
		new_value += ", ";
	    arrow = !arrow;
	}

	first_elem = false;

	new_value += line;
    }

    delete[] lines;

    if (!new_value.contains('(', 0))
	new_value = '(' + new_value + ')';

    value = new_value;
}

// Bring VALUE of VAR into a form understood by DDD
void GDBAgent::munch_value(string& value, const string& var) const
{
    while (value.contains(var + " = ", 0))
	value = value.after(" = ");
    strip_leading_space(value);

    if (gdb->type() != PERL || !value.contains(rxint, 0))
	return;

    // Special treatment
    if (!var.empty() && var[0] == '@')
	munch_perl_array(value, false);
    else if (!var.empty() && var[0] == '%')
	munch_perl_array(value, true);
    else
	munch_perl_scalar(value);
}



//-----------------------------------------------------------------------------
// Handle error messages
//-----------------------------------------------------------------------------

void GDBAgent::PanicHP(Agent *source, void *, void *call_data)
{
    string msg = STATIC_CAST(char *,call_data);
    string path = source->path();
    GDBAgent *gdb = ptr_cast(GDBAgent, source);
    if (gdb != 0)
	path = downcase(gdb->title());
    std::cerr << path << ": " << msg << "\n";
}

void GDBAgent::StrangeHP(Agent *source, void *client_data, void *call_data)
{
    string msg = STATIC_CAST(char *,call_data);
    msg.prepend("warning: ");
    PanicHP(source, client_data, CONST_CAST(char*,msg.chars()));
}

// Terminator
void GDBAgent::abort()
{
    // Clean up now
    TTYAgent::abort();

    // Reset state (in case we're restarted)
    state             = BusyOnInitialCmds;
    _verbatim         = false;
    _recording        = false;
    _detect_echos     = true;
    last_prompt       = "";
    last_written      = "";
    echoed_characters = -1;
    questions_waiting = false;
    complete_answer   = "";

    set_exception_state(false);
}
