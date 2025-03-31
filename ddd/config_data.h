// DDD configuration data

// Copyright (C) 2055 Free Software Foundation, Inc.
// Written by Michael Eager <eager@gnu.org>
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

#include "AppData.h"

// Describe map between external name (e.g., gdb.init.command)
// and location in internal app_data.
// NB:  Only handle string data
struct AppDataFormat 
{
    const char *XMLname;    // Name in XML settings file
    const char **AppData;    // Target in app_data
};

#define APP_DATA(xml,target) { xml, &app_data.target }

static AppDataFormat ADFormat[] = {
  APP_DATA("gdb.init.commands", gdb_init_commands),
  APP_DATA("gdb.settings", gdb_settings),
  APP_DATA("dbx.init.commands", dbx_init_commands),
  APP_DATA("dbx.settings", dbx_settings),
  APP_DATA("xdb.init.commands", xdb_init_commands),
  APP_DATA("xdb.settings", xdb_settings),
  APP_DATA("bash.init.commands", bash_init_commands),
  APP_DATA("bash.settings", bash_settings),
  APP_DATA("dbg.init.commands", dbg_init_commands),
  APP_DATA("dbg.settings", dbg_settings),
  APP_DATA("jdb.init.commands", jdb_init_commands),
  APP_DATA("jdb.settings", jdb_settings),
  APP_DATA("make.init.commands", make_init_commands),
  APP_DATA("make.settings", make_settings),
  APP_DATA("perl.init.commands", perl_init_commands),
  APP_DATA("perl.settings", perl_settings),
  APP_DATA("pydb.init.commands", pydb_init_commands),
  APP_DATA("pydb.settings", pydb_settings),
  { 0, 0 }
};

    
