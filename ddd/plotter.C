// $Id$ -*- C++ -*-
// Create a plotter interface

// Copyright (C) 1998 Technische Universitaet Braunschweig, Germany.
// Copyright (C) 2001, 2003 Free Software Foundation, Inc.
// Written by Andreas Zeller <zeller@gnu.org>.
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

char plotter_rcsid[] = 
    "$Id$";

#include "plotter.h"

#include "base/assert.h"
#include "x11/charsets.h"
#include "base/cook.h"
#include "ddd.h"
#include "exit.h"
#include "x11/findParent.h"
#include "file.h"
#include "filetype.h"
#include "fonts.h"
#include "post.h"
#include "print.h"
#include "regexps.h"
#include "simpleMenu.h"
#include "status.h"
#include "base/strclass.h"
#include "string-fun.h"
#include "tempfile.h"
#include "x11/verify.h"
#include "version.h"
#include "wm.h"
#include "AppData.h"
#include "Command.h"
#include "x11/Delay.h"
#include "x11/DeleteWCB.h"
#include "HelpCB.h"
#include "motif/MakeMenu.h"
#include "DispValue.h"
#include "DataDisp.h"
#include "x11/DestroyCB.h"
#include "agent/TimeOut.h"
#include "darkmode.h"

#include <stdio.h>
#include <fstream>
#include <vector>

#include <Xm/Command.h>
#include <Xm/MainW.h>
#include <Xm/MessageB.h>
#include <Xm/AtomMgr.h>
#include <Xm/FileSB.h>
#include <Xm/DrawingA.h>
#include <Xm/ScrolledW.h>
#include <Xm/SelectioB.h>
#include <Xm/ScrollBar.h>
#include <Xm/Text.h>
#include <Xm/TextF.h>
#include <Xm/ToggleB.h>

static void TraceInputHP (Agent *source, void *, void *call_data);
static void TraceOutputHP(Agent *source, void *, void *call_data);
static void TraceErrorHP (Agent *source, void *, void *call_data);
static void SetStatusHP  (Agent *source, void *, void *call_data);
static void PlotterNotFoundHP(Agent *source, void *, void *call_data);

static void CancelPlotCB(Widget, XtPointer, XtPointer);

static void SelectPlotCB(Widget, XtPointer, XtPointer);
static void SelectAndPrintPlotCB(Widget, XtPointer, XtPointer);

static void ReplotCB(Widget, XtPointer, XtPointer);
static void PlotCommandCB(Widget, XtPointer, XtPointer);

static void ToggleOptionCB(Widget, XtPointer, XtPointer);
static void ToggleLogscaleCB(Widget, XtPointer, XtPointer);
static void SetStyleCB(Widget, XtPointer, XtPointer);
static void SetContourCB(Widget, XtPointer, XtPointer);

struct PlotWindowInfo {
    DispValue *source = nullptr;            // The source we depend upon
    string window_name = "";                // The window name
    PlotAgent *plotter = nullptr;	    // The current Gnuplot instance
    Widget shell = 0;	                    // The shell we're in
    Widget gnuplot = 0;                     // The Gnuplot window
    Widget command = 0;                     // Command widget
    Widget command_dialog = 0;              // Command dialog

    string settings = "";                   // Plot settings
    XtIntervalId settings_timer = 0;        // Wait for settings
    string settings_file = "";              // File to get settings from
    StatusDelay *settings_delay = nullptr;  // Delay while getting settings
};


//-------------------------------------------------------------------------
// Menus
//-------------------------------------------------------------------------

static MMDesc file_menu[] = 
{
    { "command", MMPush, { PlotCommandCB, 0 }, 0, 0, 0, 0 },
    MMSep,
    { "replot",  MMPush, { ReplotCB, 0 }, 0, 0, 0, 0 },
    { "print",   MMPush, { SelectAndPrintPlotCB, 0 }, 0, 0, 0, 0 },
    MMSep,
    { "close",   MMPush, { CancelPlotCB, 0 }, 0, 0, 0, 0 },
    MMEnd
};

static MMDesc view_menu[] = 
{
    { "border",    MMToggle, { ToggleOptionCB, 0 }, 0, 0, 0, 0 },
    { "timestamp",      MMToggle, { ToggleOptionCB, 0 }, 0, 0, 0, 0 },
    MMSep,
    { "grid",      MMToggle, { ToggleOptionCB, 0 }, 0, 0, 0, 0 },
    { "xzeroaxis", MMToggle, { ToggleOptionCB, 0 }, 0, 0, 0, 0 },
    { "yzeroaxis", MMToggle, { ToggleOptionCB, 0 }, 0, 0, 0, 0 },
    MMEnd
};

static MMDesc contour_menu[] = 
{
    { "base",      MMToggle, { SetContourCB, 0 }, 0, 0, 0, 0 },
    { "surface",   MMToggle, { SetContourCB, 0 }, 0, 0, 0, 0 },
    MMEnd
};

static MMDesc scale_menu[] = 
{
    { "logscale",  MMToggle, { ToggleLogscaleCB, 0 }, 0, 0, 0, 0 },
    MMSep,
    { "xtics",     MMToggle, { ToggleOptionCB, 0 }, 0, 0, 0, 0 },
    { "ytics",     MMToggle, { ToggleOptionCB, 0 }, 0, 0, 0, 0 },
    { "ztics",     MMToggle, { ToggleOptionCB, 0 }, 0, 0, 0, 0 },
    MMEnd
};

static MMDesc plot_menu[] = 
{
    { "points",         MMToggle, { SetStyleCB, 0 }, 0, 0, 0, 0 },
    { "lines",          MMToggle, { SetStyleCB, 0 }, 0, 0, 0, 0 },
    { "lines3d",        MMToggle, { SetStyleCB, 0 }, 0, 0, 0, 0 },
    { "linespoints",    MMToggle, { SetStyleCB, 0 }, 0, 0, 0, 0 },
    { "linespoints3d",  MMToggle | MMUnmanaged, 
                                  { SetStyleCB, 0 }, 0, 0, 0, 0 },
    { "impulses",       MMToggle, { SetStyleCB, 0 }, 0, 0, 0, 0 },
    { "dots",           MMToggle, { SetStyleCB, 0 }, 0, 0, 0, 0 },
    { "steps2d",        MMToggle, { SetStyleCB, 0 }, 0, 0, 0, 0 },
    { "boxes2d",        MMToggle, { SetStyleCB, 0 }, 0, 0, 0, 0 },
    MMEnd
};

static MMDesc menubar[] = 
{
    { "file",     MMMenu,          MMNoCB, file_menu,        0, 0, 0 },
    { "edit",     MMMenu,          MMNoCB, simple_edit_menu, 0, 0, 0 },
    { "plotView", MMMenu,          MMNoCB, view_menu,        0, 0, 0 },
    { "plot",     MMRadioMenu,     MMNoCB, plot_menu,        0, 0, 0 },
    { "scale",    MMMenu,          MMNoCB, scale_menu,       0, 0, 0 },
    { "contour",  MMMenu,          MMNoCB, contour_menu,     0, 0, 0 },
    { "help",     MMMenu | MMHelp, MMNoCB, simple_help_menu, 0, 0, 0 },
    MMEnd
};


static void configure_plot(PlotWindowInfo *plot);


//-------------------------------------------------------------------------
// Plotter commands
//-------------------------------------------------------------------------

static void send(PlotWindowInfo *plot, const string& cmd)
{
    data_disp->select(plot->source);
    plot->plotter->write(cmd.chars(), cmd.length());
}

static void send_and_replot(PlotWindowInfo *plot, string cmd)
{
    if (cmd.matches(rxwhite))
	return;

    if (!cmd.contains('\n', -1))
	cmd += "\n";
    if (cmd.contains("help", 0))
	cmd += "\n";		// Exit `help'
    else
	cmd += "replot\n";

    send(plot, cmd);
}


//-------------------------------------------------------------------------
// Set up menu
//-------------------------------------------------------------------------

static void slurp_file(const string& filename, string& target)
{
    std::ifstream is(filename.chars());
    if (is.bad())
    {
	target = "";
	return;
    }

    std::ostringstream s;
    int c;
    while ((c = is.get()) != EOF)
	s << (unsigned char)c;

    target = s;
}

static void GetPlotSettingsCB(XtPointer client_data, XtIntervalId *id)
{
    (void) id;			// Use it
    PlotWindowInfo *plot = (PlotWindowInfo *)client_data;

    assert(plot->settings_timer == *id);
    plot->settings_timer = 0;

    // Check for settings file to be created
    string settings;
    slurp_file(plot->settings_file, settings);

    if (settings.contains("set zero"))
    {
	// Settings are complete
	unlink(plot->settings_file.chars());
	plot->settings = settings;

	configure_plot(plot);

	delete plot->settings_delay;
	plot->settings_delay = nullptr;
    }
    else
    {
	// Try again in 500 ms
	plot->settings_timer = 
	    XtAppAddTimeOut(XtWidgetToApplicationContext(plot->shell), 500, 
			    GetPlotSettingsCB, XtPointer(plot));
    }
}

static void configure_options(PlotWindowInfo *plot, MMDesc *menu, 
			      const string& settings)
{
    for (int i = 0; menu[i].name != 0; i++)
    {
	if ((menu[i].type & MMTypeMask) != MMToggle)
	    continue;

	string name = menu[i].name;

	const string s1 = "*" + name;
	Widget w = XtNameToWidget(plot->shell, s1.chars());
	XtCallbackProc callback = menu[i].callback.callback;

	bool set = false;
	if (callback == ToggleOptionCB)
	{
	    set = settings.contains("\nset " + name);
            if (settings.contains("\nset " + name + " \"\""))
                set = false;

	}
	else if (callback == SetContourCB)
	{
	    if (name == "base")
		set = settings.contains("\nset contour base\n") ||
		    settings.contains("\nset contour both\n");
	    else if (name == "surface")
		set = settings.contains("\nset contour surface\n") ||
		    settings.contains("\nset contour both\n");
	}
	else if (callback == ToggleLogscaleCB)
	{
	    set = settings.contains("\nset logscale");
	}

	XmToggleButtonSetState(w, set, False);
    }
}

static void configure_plot(PlotWindowInfo *plot)
{
    if (plot->plotter == 0)
	return;

    int ndim = plot->plotter->dimensions();

    // Set up plot menu
    int i;
    for (i = 0; plot_menu[i].name != 0; i++)
    {
	if ((plot_menu[i].type & MMTypeMask) != MMToggle)
	    continue;

	string name = plot_menu[i].name;

	const string s1 = "*" + name;
	Widget w = XtNameToWidget(plot->shell, s1.chars());

	if (name.contains("2d", -1))
	    XtSetSensitive(w, ndim == 2);
	else if (name.contains("3d", -1))
	    XtSetSensitive(w, ndim >= 3);
	else
	    XtSetSensitive(w, ndim >= 2);
    }

    // Log scale is available only iff all values are non-negative
    Widget logscale = XtNameToWidget(plot->shell, "*logscale");
    XtSetSensitive(logscale, True);

    // Axes can be toggled in 2d mode only
    Widget xzeroaxis = XtNameToWidget(plot->shell, "*xzeroaxis");
    Widget yzeroaxis = XtNameToWidget(plot->shell, "*yzeroaxis");
    XtSetSensitive(xzeroaxis, ndim <= 2);
    XtSetSensitive(yzeroaxis, ndim <= 2);

    // Z Tics are available in 3d mode only
    Widget ztics = XtNameToWidget(plot->shell, "*ztics");
    XtSetSensitive(ztics, ndim >= 3);

    // Contour drawing is available in 3d mode only
    Widget base    = XtNameToWidget(plot->shell, "*base");
    Widget surface = XtNameToWidget(plot->shell, "*surface");
    XtSetSensitive(base,    ndim >= 3);
    XtSetSensitive(surface, ndim >= 3);

    // The remainder requires settings
    if (plot->settings.empty())
    {
	// No settings yet
	if (plot->settings_timer == 0)
	{
	    plot->settings_delay = new StatusDelay("Retrieving Plot Settings");

	    // Save settings...
	    plot->settings_file = tempfile();
	    string cmd = "save " + quote(plot->settings_file) + "\n";
	    send(plot, cmd);

	    // ...and try again in 250ms
	    plot->settings_timer = 
		XtAppAddTimeOut(XtWidgetToApplicationContext(plot->shell), 250,
				GetPlotSettingsCB, XtPointer(plot));
	}

	return;
    }

    configure_options(plot, view_menu,    plot->settings);
    configure_options(plot, contour_menu, plot->settings);
    configure_options(plot, scale_menu,   plot->settings);

    // Get style
    for (i = 0; plot_menu[i].name != 0; i++)
    {
	if ((plot_menu[i].type & MMTypeMask) != MMToggle)
	    continue;

	string name = plot_menu[i].name;

	const string s1 = "*" + name;
	Widget w = XtNameToWidget(plot->shell, s1.chars());

	bool set = plot->settings.contains("\nset style data " + name + "\n");
	XmToggleButtonSetState(w, set, False);
    }
}



//-------------------------------------------------------------------------
// Decoration stuff
//-------------------------------------------------------------------------

// Start plot
static void popup_plot_shell(PlotWindowInfo *plot)
{
    // Fetch plot settings
    configure_plot(plot);

    // Command and export dialogs are not needed (yet)
    if (plot->command_dialog != 0)
        XtUnmanageChild(plot->command_dialog);

    // Pop up shell
    XtSetSensitive(plot->shell, True);
    XtPopup(plot->shell, XtGrabNone);
    wait_until_mapped(plot->shell);
}

// Cancel plot
static void popdown_plot_shell(PlotWindowInfo *plot)
{
    static bool entered = false;
    if (entered)
	return;

    entered = true;

    // Manage dialogs
    if (plot->command_dialog != nullptr)
	XtUnmanageChild(plot->command_dialog);

    if (plot->shell != nullptr && XtWindow(plot->shell)!=0)
    {
	XWithdrawWindow(XtDisplay(plot->shell), XtWindow(plot->shell),
			XScreenNumberOfScreen(XtScreen(plot->shell)));
	XtPopdown(plot->shell);

	// XtPopdown may not withdraw an iconified shell.  Hence, make
	// sure the shell really becomes disabled.
	XtSetSensitive(plot->shell, False);
    }

    // Manage settings
    if (plot->settings_timer != 0)
    {
	// Still waiting for settings
	XtRemoveTimeOut(plot->settings_timer);
	plot->settings_timer = 0;

	unlink(plot->settings_file.chars());
    }

    if (plot->settings_delay != nullptr)
    {
	plot->settings_delay->outcome = "canceled";
	delete plot->settings_delay;
	plot->settings_delay = nullptr;
    }

    plot->settings = "";

    entered = false;
}

static void CancelPlotCB(Widget, XtPointer client_data, XtPointer)
{
    static bool entered = false;
    if (entered)
	return;

    entered = true;

    PlotWindowInfo *plot = (PlotWindowInfo *)client_data;
    popdown_plot_shell(plot);

    if (plot->plotter != 0)
    {
	// Terminate plotter
	plot->plotter->removeHandler(Died, PlotterNotFoundHP, client_data);
	plot->plotter->terminate();
	plot->plotter = 0;
    }

    entered = false;
}

static void DeletePlotterCB(XtPointer client_data, XtIntervalId *)
{
    Agent *plotter = (Agent *)client_data;
    delete plotter;
}

static void DeletePlotterHP(Agent *plotter, void *client_data, void *)
{
    // Defer deletion to the Xt event loop (0 ms timeout) so that DispValue is notified
    // and can clear its plotter pointer before the plotter is actually destroyed.
    XtAppAddTimeOut(XtWidgetToApplicationContext(gdb_w), 0,
		    DeletePlotterCB, XtPointer(plotter));

    plotter->removeHandler(Died, DeletePlotterHP, client_data);

    PlotWindowInfo *plot = (PlotWindowInfo *)client_data;
    assert(plot->plotter == 0 || plot->plotter == plotter);
    plot->plotter = 0;
    popdown_plot_shell(plot);
}

static void PlotterNotFoundHP(Agent *plotter, void *client_data, void *)
{
#if !NDEBUG
    PlotWindowInfo *plot = (PlotWindowInfo *)client_data;
    assert(plot->plotter == 0 || plot->plotter == plotter);
#endif

    plotter->removeHandler(Died, PlotterNotFoundHP, client_data);

    string base = app_data.plot_command;
    if (base.contains(' '))
	base = base.before(' ');

    Arg args[10];
    Cardinal arg = 0;
    MString msg = rm( capitalize(base) + " could not be started.");
    XtSetArg(args[arg], XmNmessageString, msg.xmstring()); arg++;
    Widget dialog = 
	verify(XmCreateErrorDialog(find_shell(),
				   XMST("no_plotter_dialog"), args, arg));
    XtUnmanageChild(XmMessageBoxGetChild
		    (dialog, XmDIALOG_CANCEL_BUTTON));
    XtAddCallback(dialog, XmNhelpCallback, ImmediateHelpCB, XtPointer(0));

    Delay::register_shell(dialog);
    manage_and_raise(dialog);
}

static std::vector<PlotWindowInfo*> plot_infos;

static PlotWindowInfo *new_decoration(const string& name)
{
    PlotWindowInfo *plot = 0;

    // Check whether we can reuse an existing decoration
    for (int i = 0; i < int(plot_infos.size()); i++)
    {
	PlotWindowInfo *info = plot_infos[i];
	if (info->plotter == 0)
	{
	    // Shell is unused - use this one
	    plot = info;
	    break;
	}
    }

    if (plot == nullptr)
    {
	plot = new PlotWindowInfo;

	// Create decoration windows
	Arg args[10];
	Cardinal arg = 0;
	XtSetArg(args[arg], XmNallowShellResize, True);       arg++;
	XtSetArg(args[arg], XmNdeleteResponse, XmDO_NOTHING); arg++;

	plot->shell = verify(XtCreateWidget("plot", topLevelShellWidgetClass,
					    find_shell(), args, arg));

	AddDeleteWindowCallback(plot->shell, CancelPlotCB, XtPointer(plot));

	arg = 0;
	Widget main_window = XmCreateMainWindow(plot->shell, 
						XMST("main_window"), 
						args, arg);
	XtManageChild(main_window);

	MMcreateMenuBar(main_window, "menubar", menubar);
	MMaddCallbacks(file_menu,    XtPointer(plot));
	MMaddCallbacks(simple_edit_menu);
	MMaddCallbacks(view_menu,    XtPointer(plot));
	MMaddCallbacks(plot_menu,    XtPointer(plot));
	MMaddCallbacks(scale_menu,   XtPointer(plot));
	MMaddCallbacks(contour_menu, XtPointer(plot));
	MMaddCallbacks(simple_help_menu);
	MMaddHelpCallback(menubar, ImmediateHelpCB);

        setColorMode(main_window, app_data.dark_mode);

        // Create work window
        plot->gnuplot = XtVaCreateManagedWidget("plotArea", xmDrawingAreaWidgetClass, main_window,
                                                  XmNwidth, 640,
                                                  XmNheight, 480,
                                                  NULL);
        XtManageChild(plot->gnuplot);

	Delay::register_shell(plot->shell);
	InstallButtonTips(plot->shell);

	plot_infos.push_back(plot);
    }

    string title = DDD_NAME ": " + name;
    XtVaSetValues(plot->shell,
		  XmNtitle, title.chars(),
		  XmNiconName, title.chars(),
		  XtPointer(0));

    return plot;
}

// Remove all unused decorations from cache
void clear_plot_window_cache()
{
    for (int i = 0; i < int(plot_infos.size()); i++)
    {
	PlotWindowInfo *info = plot_infos[i];
	if (info->plotter == 0)
	{
	    // Shell is unused -- destroy it
	    XtDestroyWidget(info->shell);
	    info->shell = 0;
	}
	else
	{
	    // A running shell should be destroyed after invocation.
	    // (FIXME)
	}
    }

    plot_infos.clear();
}

// Delete plot window
void delete_plotter(PlotAgent *plotter)
{
    plotter->removeAllHandlers();
    plotter->terminate();
    delete plotter;
}

// Create a new plot window
PlotAgent *new_plotter(const string& name, DispValue *source)
{
    // Create shell
    PlotWindowInfo *plot = new_decoration(name);
    if (plot == 0)
        return 0;

    popup_plot_shell(plot);
    string cmd = app_data.plot_command;
    cmd.gsub("@FONT@", make_xftfont(app_data, FixedWidthDDDFont));

    string window_name = ddd_NAME "plot";
    if (cmd.contains("@NAME@"))
        cmd.gsub("@NAME@", window_name);
    else
        cmd += " -name " + window_name;

    Window win = XtWindow(plot->gnuplot);   // Must be valid (widget realized)
    char hex[32];
    snprintf(hex, sizeof(hex), "%lx", (unsigned long)win);

    cmd.gsub("@X_ID@", hex);

    plot->source      = source;
    plot->window_name = window_name;

    // Invoke plot process
    PlotAgent *plotter = 
	new PlotAgent(XtWidgetToApplicationContext(plot->shell), cmd);

    XtAddCallback(plot->shell, XtNpopdownCallback, CancelPlotCB, XtPointer(plot));

    // Add trace handlers
    plotter->addHandler(Input,  TraceInputHP);     // Gnuplot => DDD
    plotter->addHandler(Output, TraceOutputHP);    // DDD => Gnuplot
    plotter->addHandler(Error,  TraceErrorHP);     // Gnuplot Errors => DDD

    // Show Gnuplot Errors in status line
    plotter->addHandler(Error,  SetStatusHP,       (void *)plot);

    // Handle death
    plotter->addHandler(Died, PlotterNotFoundHP, (void *)plot);
    plotter->addHandler(Died, DeletePlotterHP,   (void *)plot);

    string init = app_data.plot_init_commands;

    if (!init.empty() && !init.contains('\n', -1))
	init += '\n';

    plotter->start_with(init);
    plot->plotter = plotter;

    return plotter;
}



//-------------------------------------------------------------------------
// Selection stuff
//-------------------------------------------------------------------------

static void SelectPlotCB(Widget, XtPointer client_data, XtPointer)
{
    PlotWindowInfo *plot = (PlotWindowInfo *)client_data;

    data_disp->select(plot->source);
}

static void SelectAndPrintPlotCB(Widget w, XtPointer client_data, 
				 XtPointer call_data)
{
    SelectPlotCB(w, client_data, call_data);
    PrintPlotCB(w, client_data, call_data);
}



//-------------------------------------------------------------------------
// Plot again
//-------------------------------------------------------------------------

static void ReplotCB(Widget, XtPointer client_data, XtPointer)
{
    PlotWindowInfo *plot = (PlotWindowInfo *)client_data;

    // This transfers the data once again and replots the whole thing
    plot->source->plot();
}

//-------------------------------------------------------------------------
// Command
//-------------------------------------------------------------------------

// Selection from Command widget
static void DoPlotCommandCB(Widget, XtPointer client_data, XtPointer call_data)
{
    PlotWindowInfo *plot = (PlotWindowInfo *)client_data;
    XmCommandCallbackStruct *cbs = (XmCommandCallbackStruct *)call_data;

    MString xcmd(cbs->value, true);
    string cmd = xcmd.str();

    send_and_replot(plot, cmd);
}

// Apply button
static void ApplyPlotCommandCB(Widget, XtPointer client_data, XtPointer)
{
    PlotWindowInfo *plot = (PlotWindowInfo *)client_data;

    Widget text = XmCommandGetChild(plot->command, XmDIALOG_COMMAND_TEXT);
    String cmd_s = 0;

    if (XmIsTextField(text))
	cmd_s = XmTextFieldGetString(text);
    else if (XmIsText(text))
	cmd_s = XmTextGetString(text);
    else {
        assert(0);
	::abort();
    }

    string cmd = cmd_s;
    XtFree(cmd_s);

    send_and_replot(plot, cmd);
}

static void EnableApplyCB(Widget, XtPointer client_data, XtPointer call_data)
{
    Widget apply = (Widget)client_data;
    XmCommandCallbackStruct *cbs = (XmCommandCallbackStruct *)call_data;

    set_sensitive(apply, cbs->length > 0);
}

static void PlotCommandCB(Widget, XtPointer client_data, XtPointer)
{
    PlotWindowInfo *plot = (PlotWindowInfo *)client_data;

    if (plot->command_dialog == 0)
    {
	Arg args[10];
	Cardinal arg = 0;
	Widget dialog = 
	    verify(XmCreatePromptDialog(plot->shell,
					XMST("plot_command_dialog"),
					args, arg));
	Delay::register_shell(dialog);
	plot->command_dialog = dialog;

	Widget apply = XmSelectionBoxGetChild(dialog, XmDIALOG_APPLY_BUTTON);
	XtManageChild(apply);
    
	XtUnmanageChild(XmSelectionBoxGetChild(dialog, 
					       XmDIALOG_OK_BUTTON));
	XtUnmanageChild(XmSelectionBoxGetChild(dialog, 
					       XmDIALOG_SELECTION_LABEL));
	XtUnmanageChild(XmSelectionBoxGetChild(dialog, XmDIALOG_TEXT));

	XtAddCallback(dialog, XmNapplyCallback,
		      ApplyPlotCommandCB, XtPointer(client_data));
	XtAddCallback(dialog, XmNhelpCallback,
		      ImmediateHelpCB, XtPointer(client_data));

	arg = 0;
	Widget command = 
	    verify(XmCreateCommand(dialog, XMST("plot_command"), args, arg));
	plot->command = command;
	XtManageChild(command);

	XtAddCallback(command, XmNcommandEnteredCallback, 
		      DoPlotCommandCB, XtPointer(client_data));
	XtAddCallback(command, XmNcommandChangedCallback, 
		      EnableApplyCB, XtPointer(apply));
	set_sensitive(apply, false);
    }

    manage_and_raise(plot->command_dialog);
}

//-------------------------------------------------------------------------
// Settings
//-------------------------------------------------------------------------

static void ToggleOptionCB(Widget w, XtPointer client_data, 
			   XtPointer call_data)
{
    PlotWindowInfo *plot = (PlotWindowInfo *)client_data;
    XmToggleButtonCallbackStruct *cbs = 
	(XmToggleButtonCallbackStruct *)call_data;

    string cmd;
    if (cbs->set)
	cmd = string("set ") + XtName(w);
    else
	cmd = string("unset ") + XtName(w);

    send_and_replot(plot, cmd);
}

static void ToggleLogscaleCB(Widget, XtPointer client_data, 
			     XtPointer call_data)
{
    PlotWindowInfo *plot = (PlotWindowInfo *)client_data;
    XmToggleButtonCallbackStruct *cbs = 
	(XmToggleButtonCallbackStruct *)call_data;

    string cmd;
    if (cbs->set)
	cmd = "set logscale ";
    else
	cmd = "unset logscale ";

    if (plot->plotter->dimensions() >= 3)
	cmd += "z";
    else
	cmd += "y";

    send_and_replot(plot, cmd);
}

static void SetStyleCB(Widget w, XtPointer client_data, XtPointer call_data)
{
    PlotWindowInfo *plot = (PlotWindowInfo *)client_data;
    XmToggleButtonCallbackStruct *cbs = 
	(XmToggleButtonCallbackStruct *)call_data;

    if (cbs->set)
    {
	string style = XtName(w);
	string cmd;
	if (style.contains("3d", -1))
	{
	    cmd = "set hidden3d\n";
	    style = style.before("3d");
	}
	else
	{
	    cmd = "unset hidden3d\n";
	}
	if (style.contains("2d", -1))
	    style = style.before("2d");
	
	cmd += "set style data " + style;

	send_and_replot(plot, cmd);
    }
}

static void SetContourCB(Widget w, XtPointer client_data, XtPointer)
{
    PlotWindowInfo *plot = (PlotWindowInfo *)client_data;

    Widget base    = XtNameToWidget(XtParent(w), "base");
    Widget surface = XtNameToWidget(XtParent(w), "surface");

    assert (base != 0 && surface != 0);

    bool base_set    = XmToggleButtonGetState(base);
    bool surface_set = XmToggleButtonGetState(surface);

    string cmd;
    if (base_set && surface_set)
	cmd = "set contour both";
    else if (base_set && !surface_set)
	cmd = "set contour base";
    else if (!base_set && surface_set)
	cmd = "set contour surface";
    else
	cmd = "set nocontour";

    send_and_replot(plot, cmd);
}

//-------------------------------------------------------------------------
// Status line
//-------------------------------------------------------------------------

// Forward Gnuplot error messages to DDD status line
static void SetStatusHP(Agent *, void *client_data, void *call_data)
{
    PlotWindowInfo *plot = (PlotWindowInfo *)client_data;
    DataLength* dl = (DataLength *) call_data;
    string s(dl->data, dl->length);

    if (plot->command != 0)
    {
	string msg = s;
	strip_space(msg);
	MString xmsg = tb(msg);
	XmCommandError(plot->command, xmsg.xmstring());
    }

    while (!s.empty())
    {
	string line;
	if (s.contains('\n'))
	    line = s.before('\n');
	else
	    line = s;
	s = s.after('\n');
	strip_space(line);

	if (!line.empty())
	    set_status(line);
    }
}

//-------------------------------------------------------------------------
// Trace communication
//-------------------------------------------------------------------------

static void trace(const char *prefix, void *call_data)
{
    DataLength* dl = (DataLength *) call_data;
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
	s.at((int)(s.length() - 1), 0) = "\\n";

    dddlog << prefix << s << '\n';
    dddlog.flush();
}

static void TraceInputHP(Agent *, void *, void *call_data)
{
    trace("<< ", call_data);
}

static void TraceOutputHP(Agent *, void *, void *call_data)
{
    trace(">> ", call_data);
}

static void TraceErrorHP(Agent *, void *, void *call_data)
{
    trace("<= ", call_data);
}
