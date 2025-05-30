// $Id$
// Read and store type and value of a displayed expression

// Copyright (C) 1995-1998 Technische Universitaet Braunschweig, Germany.
// Copyright (C) 2000-2001 Universitaet Passau, Germany.
// Copyright (C) 2001, 2003 Free Software Foundation, Inc.
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

char DispValue_rcsid[] =
    "$Id$";

#ifndef LOG_CREATE_VALUES
#define LOG_CREATE_VALUES 0
#endif


//-----------------------------------------------------------------------------
// A `DispValue' maintains type and value of a displayed expression
//-----------------------------------------------------------------------------

#include "DispValue.h"

#include "AppData.h"
#include "DispNode.h"
#include "GDBAgent.h"
#include "PlotAgent.h"
#include "base/assert.h"
#include "base/cook.h"
#include "ddd.h"
#include "deref.h"
#include "fonts.h"
#include "base/isid.h"
#include "base/misc.h"
#include "plotter.h"
#include "question.h"
#include "regexps.h"
#include "string-fun.h"
#include "value-read.h"
#include "status.h"

#include <ctype.h>
#include <stdlib.h>

#include <algorithm>


//-----------------------------------------------------------------------------
// Helpers
//-----------------------------------------------------------------------------

int DispValue::m_cached_box_tics = 0;

StringStringAssoc DispValue::type_cache;

// Get index base of expr EXPR in dimension DIM
int DispValue::index_base(const string& expr, int dim)
{
    if (gdb->program_language() != LANGUAGE_FORTRAN)
	return gdb->default_index_base();

    string base = expr;
    if (base.contains('('))
	base = base.before('(');
    if (!type_cache.has(base))
	type_cache[base] = gdb_question(gdb->whatis_command(base));
    string type = type_cache[base];

    // GDB issues array information as `type = real*8 (0:9,2:12)'.
    // However, the first dimension in the type output comes last in
    // the printed array.
    int colon = type.length();
    while (colon >= 0 && dim-- >= 0)
	colon = type.index(':', colon - type.length() - 1);
    if (colon < 0)
	return  gdb->default_index_base(); // Not found

    while (colon >= 0 && isdigit(type[colon - 1]))
	colon--;

    return atoi(type.chars() + colon);
}

// In FORTRAN mode, GDB issues last dimensions first.  Insert new
// dimension before first dimension and convert to FORTRAN
// multi-dimension syntax.
string DispValue::add_member_name(const string& base, 
				  const string& member_name)
{
    if (gdb->program_language() == LANGUAGE_FORTRAN && 
	member_name.contains('(', 0) &&	base.contains('('))
    {
	return base.before('(') + member_name.before(')') + ", " + 
	    base.after('(');
    }

    return base + member_name;
}

void DispValue::clear_type_cache()
{
    static StringStringAssoc empty;
    type_cache = empty;
}


//-----------------------------------------------------------------------------
// Data
//-----------------------------------------------------------------------------

bool DispValue::expand_repeated_values = false;
DispValue *(*DispValue::value_hook)(string& value) = 0;


//-----------------------------------------------------------------------------
// Function defs
//-----------------------------------------------------------------------------

// Constructor
DispValue::DispValue (DispValue* parent, 
		      int depth,
		      string& value,
		      const string& f_n, 
		      const string& p_n,
		      DispValueType given_type)
    : m_type(UnknownType), m_expanded(true), m_enabled(true),
      m_full_name(f_n), m_print_name(p_n), m_addr(""), 
      m_changed(false), m_repeats(1),
      m_value(""), m_dereferenced(false), m_member_names(true), m_children(0),
      m_index_base(0), m_have_index_base(false), m_orientation(Horizontal),
      m_has_plot_orientation(false), m_plotter(0), 
      m_cached_box(0), m_cached_box_change(0),
      m_links(1)
{
    init(parent, depth, value, given_type);

    // A new display is not changed, but initialized
    m_changed = false;
}

// Duplicator
DispValue::DispValue (const DispValue& dv)
    : m_type(dv.m_type), m_expanded(dv.m_expanded), 
      m_enabled(dv.m_enabled), m_full_name(dv.m_full_name),
      m_print_name(dv.m_print_name), m_addr(dv.m_addr),
      m_changed(false), m_repeats(dv.m_repeats),
      m_value(dv.value()), m_dereferenced(false), 
      m_member_names(dv.member_names()), m_children(dv.nchildren()), 
       m_index_base(dv.m_index_base), 
      m_have_index_base(dv.m_have_index_base), m_orientation(dv.m_orientation),
      m_has_plot_orientation(false), m_plotter(0),
      m_cached_box(0), m_cached_box_change(0),
      m_links(1)
{
    for (int i = 0; i < dv.nchildren(); i++)
    {
        m_children.push_back(dv.child(i)->dup());
    }

    if (dv.cached_box() != 0)
	set_cached_box(dv.cached_box()->link());
}


// True if more sequence members are coming
bool DispValue::sequence_pending(const string& value, 
				 const DispValue *parent)
{
    if (parent != 0)
    {
	switch (parent->type())
	{
	case Sequence:
	case List:
	case Struct:
	case Reference:
	case Array:
        case UserCommand:
        case STLVector:
        case STLList:
	    // In a composite, we always read everything up to the
	    // final delimiter.
	    return false;

	case Simple:
	case Pointer:
	case Text:
	case UnknownType:
	    break;
	}
    }

    string v = value;
    strip_leading_space(v);

    if (!v.empty() && parent == 0)
	return true;		// Still more to read

    if (!is_delimited(value))
	return true;		// Not at delimiter - more stuff follows

    // Sequence is done
    return false;
}

// In Perl, replace `{$REF}' and `$REF' by `REF->'
string DispValue::normalize_base(const string& base) const
{
#if RUNTIME_REGEX
    static regex rxsimple("([][a-zA-Z0-9_$@%().`]|->)*");
#endif

    bool perl = gdb->program_language() == LANGUAGE_PERL;
    string ref = base;

    // Fetch one-letter Perl prefix
    string prefix;
    if (perl && !ref.empty() && is_perl_prefix(ref[0]))
    {
	prefix = ref[0];
	ref = ref.after(0);
    }

    // Insert `->' operators
    if (perl)
    {
	string r = ref;
	if (r.contains("{", 0) && r.contains('}', -1))
	    r = unquote(r);

	if (r.contains('$', 0) && r.matches(rxsimple))
	{
	    if (r.contains("}", -1) || r.contains("]", -1))
		ref = r.after(0); // Array between braces is optional
	    else
		ref = r.after(0) + "->";
	}
    }

    if (!perl)
    {
	// Place brackets around complex expressions
	if (!ref.matches(rxsimple))
	    ref = "(" + ref + ")";
    }

    return prefix + ref;
}

// Parsing
DispValue *DispValue::parse(DispValue *parent, 
			    int        depth,
			    string&    value,
			    const string& full_name, 
			    const string& print_name,
			    DispValueType type)
{
    if (value_hook != 0)
    {
	DispValue *dv = (*value_hook)(value);
	if (dv != 0)
	{
	    // Just take values from given element
#if LOG_CREATE_VALUES
	    std::clog << "External value " << quote(dv->full_name()) << "\n";
#endif
	    return dv;
	}
    }

    return new DispValue(parent, depth, value, full_name, print_name, type);
}

// Initialization
void DispValue::init(DispValue *parent, int depth, string& value,
		     DispValueType given_type)
{
#if LOG_CREATE_VALUES
    std::clog << "Building value from " << quote(value) << "\n";
#endif

    // Be sure the value is not changed in memory
    value.consuming(true);

    const char *initial_value = value.chars();

    m_children.clear();

    if (background(value.length()))
    {
	clear();

        m_type = Simple;
        m_value = "(Aborted)";
	value  = "Aborted\n";
	return;
    }

    m_type = given_type;
    if (m_type == UnknownType)
    {
        if ((parent == 0 || parent->type() == List || parent->type() == UserCommand) && m_print_name.empty())
            m_type = Text;
        else if (m_print_name.contains("info locals") || m_print_name.contains("info args"))
            m_type = List;
        else if (parent == 0 && is_user_command(m_print_name))
            m_type = UserCommand;
        else if (checkSTL(value, m_type)==false)
            m_type = determine_type(value);
    }

    bool ignore_repeats = (parent != 0 && parent->type() == Array);

    char perl_type = '\0';

    switch (m_type)
    {

    case Simple:
    {
	       m_value = read_simple_value(value, depth, ignore_repeats);
#if LOG_CREATE_VALUES
	std::clog << mytype << ": " << quote(_value) << "\n";
#endif
	perl_type = '$';
	break;
    }

    case Text:
    {
	// Read in a line of text
	if (value.contains('\n'))
            m_value = value.through('\n');
	else
            m_value = value;
	value = value.after('\n');
#if LOG_CREATE_VALUES
	std::clog << mytype << ": " << quote(_value) << "\n";
#endif
	perl_type = '$';
	break;
    }

    case UserCommand:
    {
	while (!value.empty())
	{
            DispValue *dv = parse_child(depth, value, m_full_name, "");

            m_children.push_back(dv);
            
	    if (background(value.length()))
	    {
		init(parent, depth, value);
		return;
	    }
            
        }
	break;
    }

    case Pointer:
    {
        m_value = read_pointer_value(value, ignore_repeats);
        m_dereferenced = false;

#if LOG_CREATE_VALUES
	std::clog << mytype << ": " << quote(_value) << "\n";
#endif
	// Hide vtable pointers.
	if (m_value.contains("virtual table") || m_value.contains("vtable"))
            m_expanded = false;
	perl_type = '$';

	// In Perl, pointers may be followed by indented `pointed to'
	// info.  Skip this.
	if (gdb->type() == PERL)
	{
	    while (value.contains("\n  ", 0))
	    {
		value = value.after("\n  ");
		value = value.from("\n");
	    }
	}		
	break;
    }

    case Array:
    {
	string base = normalize_base(m_full_name);

        m_orientation = app_data.array_orientation;

#if LOG_CREATE_VALUES
	std::clog << mytype << ": " << "\n";
#endif

	read_array_begin(value, m_addr);

	// Check for `vtable entries' prefix.
	string vtable_entries = read_vtable_entries(value);
	if (!vtable_entries.empty())
	{
            m_children.push_back(parse_child(depth, vtable_entries, m_full_name));
	}

	// Read the array elements.  Assume that the type is the
	// same across all elements.
	DispValueType member_type = UnknownType;
	if (!m_have_index_base)
	{
            m_index_base = index_base(base, depth);
            m_have_index_base = true;
	}
	int array_index = m_index_base;

	// The array has at least one element.  Otherwise, GDB
	// would treat it as a pointer.
	do {
	    const char *repeated_value = value.chars();
	    string member_name = 
		gdb->index_expr("", itostring(array_index++));
	    DispValue *dv = parse_child(depth, value,
					add_member_name(base, member_name), 
					member_name, member_type);
	    member_type = dv->type();
            m_children.push_back(dv);

	    int repeats = read_repeats(value);

	    if (expand_repeated_values)
	    {
		// Create one value per repeat
		while (--repeats > 0)
		{
		    member_name = 
			gdb->index_expr("", itostring(array_index++));
		    string val = repeated_value;
		    DispValue *repeated_dv = 
			parse_child(depth, val, 
				    add_member_name(base, member_name),
				    member_name, member_type);
                   m_children.push_back(repeated_dv);
		}
	    }
	    else
	    {
		// Show repetition in member
		if (repeats > 1)
		{
		    array_index--;

#if 0
		    // We use the GDB `artificial array' notation here,
		    // since repeat recognition is supported in GDB only.
		    member_name += "@" + itostring(repeats);

		    dv->full_name() = add_member_name(base, member_name);
		    dv->name()      = member_name;
#endif
		    dv->repeats()   = repeats;

		    array_index += repeats;
		}
	    }

	    if (background(value.length()))
	    {
		init(parent, depth, value);
		return;
	    }
	} while (read_array_next(value));
	read_array_end(value);

	// Expand only if at top-level.
        m_expanded = (depth == 0 || nchildren() <= 1 || (depth == 1 && parent->type() == STLVector));

#if LOG_CREATE_VALUES
	std::clog << mytype << " has " << nchildren() << " members\n";
#endif
	perl_type = '@';
	break;
    }

    case List:
	// Some DBXes issue the local variables via a frame line, just
	// like `set_date(d = 0x10003060, day_of_week = Sat, day = 24,
	// month = 12, year = 1994)'.  Make this more readable.
	gdb->clean_frame_line (value);

	// FALL THROUGH
    case Struct:
    {
        m_orientation  = app_data.struct_orientation;
        m_member_names = app_data.show_member_names;

	bool found_struct_begin   = false;
	bool read_multiple_values = false;
	
#if LOG_CREATE_VALUES
	std::clog << mytype << " " << quote(myfull_name) << "\n";
#endif
	string member_prefix = m_full_name;
	string member_suffix = "";
	if (m_type == List)
	{
	    member_prefix = "";
	    read_multiple_values = true;
	}
	else
	{
	    // In C and Java, `*' binds tighter than `.'
	    if (member_prefix.contains('*', 0))
	    {
		if (gdb->program_language() == LANGUAGE_C)
		{
		    // Use the C `->' operator instead
		    member_prefix.del("*");
		    if (member_prefix.contains('(', 0) &&
			member_prefix.contains(')', -1))
			member_prefix = unquote(member_prefix);

#if RUNTIME_REGEX
		    static regex rxchain("[-a-zA-Z0-9::_>.`]+");
#endif
		    if (member_prefix.matches(rxchain))
		    {
			// Simple chain of identifiers - prepend `->'
			member_prefix += "->";
		    }
		    else
		    {
			member_prefix.prepend("(");
			member_prefix += ")->";
		    }
		}
		else
		{
		    member_prefix.prepend("(");
		    member_prefix += ").";
		}
	    }
	    else if (gdb->program_language() == LANGUAGE_PERL)
	    {
		// In Perl, members of A are accessed as A{'MEMBER_NAME'}
		member_prefix = normalize_base(member_prefix) + "{'";
		member_suffix = "'}";
	    }
	    else if (gdb->program_language() == LANGUAGE_PHP)
	    {
		// In PHP, members of $A are accessed as $A['MEMBER_NAME']
		member_prefix = normalize_base(member_prefix) + "['";
		member_suffix = "']";
	    }
	    else if (gdb->program_language() == LANGUAGE_FORTRAN)
	    {
		// In Fortran, members of A are accessed as A%B
		member_prefix = normalize_base(member_prefix) + "%";
	    }
	    else
	    {
		// In all other languages, members are accessed as A.B
		member_prefix = normalize_base(member_prefix) + ".";
	    }

	    // In case we do not find a struct beginning, read only one value
	    found_struct_begin = read_struct_begin(value, m_addr);
	    read_multiple_values = found_struct_begin;
	}

	// Prepend base class in case of multiple inheritance
	// FIXME: This should be passed as an argument
	static string baseclass_prefix;
	member_prefix += baseclass_prefix;
	int base_classes = 0;

	bool more_values = true;
	while (more_values)
	{
	    // In a List, we may have `member' names like `(a + b)'.
	    // Don't be picky about this.
	    bool picky = (m_type == Struct);
	    string member_name = read_member_name(value, picky);

	    if (member_name.empty())
	    {
		// Some struct stuff that is not a member
		DispValue *dv = parse_child(depth, value, m_full_name, "");

		if (dv->type() == Struct)
		{
		    // What's this - a struct within a struct?  Just
		    // adopt the members.
		    // (This happens when we finally found the struct
		    // after having read all the AIX DBX base classes.)
		    for (int i = 0; i < dv->nchildren(); i++)
		    {
			DispValue *dv2 = dv->child(i)->link();
                        m_children.push_back(dv2);
		    }
		    dv->unlink();
		}
		else
		{
                    m_children.push_back(dv);
		}

		more_values = read_multiple_values && read_struct_next(value);
	    }
	    else if (is_BaseClass_name(member_name))
	    {
		// Base class member
		string saved_baseclass_prefix = baseclass_prefix;
		base_classes++;

		if (base_classes > 1)
		{
		    // Multiple inheritance.  Be sure to
		    // reference further members unambiguously.
		    //
		    // Note: we don't do that for the first base class,
		    // because this might turn ambiguous again.
		    //
		    // Example:
		    //
		    //    Base
		    //    |   |
		    //    I1 I2
		    //     \ /
		    //      C
		    //
		    // Members of I1::Base are not prefixed, members
		    // of I2::Base get `I2::' as base class prefix.
		    // If we did this already for the first base class,
		    // members of both I1 and I2 would get `Base::' as
		    // base class prefix.

		    switch (gdb->program_language())
		    {
		    case LANGUAGE_C: // C++
			baseclass_prefix = unquote(member_name) + "::";
			break;

		    default:
			// Do nothing (yet)
			break;
		    }
		}

		DispValue *dv = parse_child(depth, value, m_full_name, member_name);
                m_children.push_back(dv);

		baseclass_prefix = saved_baseclass_prefix;

		more_values = read_multiple_values && read_struct_next(value);

		// Skip a possible `members of CLASS:' prefix
		read_members_prefix(value);

		// AIX DBX does not place a separator between base
		// classes and the other members, so we always
		// continue reading after having found a base
		// class.  After all, the own class members are
		// still missing.
		if (m_type == Struct && !found_struct_begin)
		    more_values = true;
	    }
	    else
	    {
		// Ordinary member
		string full_name = "";

		if (member_name == " ")
		{
		    // Anonymous union
		    full_name = m_full_name;
		}
		
		if (member_name.contains('.'))
		{
		    if (gdb->has_quotes())
		    {
			// The member name contains `.' => quote it.  This
			// happens with vtable pointers on Linux (`_vptr.').
			full_name = member_prefix + quote(member_name, '\'') + 
			    member_suffix;
		    }
		    else
		    {
			// JDB (and others?) prepend the class name 
			// to inherited members.  Omit this.
			full_name = 
			    member_prefix + member_name.after('.', -1) + 
			    member_suffix;
		    }
		}
		
		if (full_name.empty())
		{
		    // Ordinary member
		    full_name = member_prefix + member_name + member_suffix;
		}

		DispValue *child = parse_child(depth, value, full_name, member_name);

		if (child->type() == Text)
		{
		    // Found a text as child - child value must be empty
		    string empty = "";
                    m_children.push_back(parse_child(depth, empty, full_name, member_name));

		    string v = child->value();
		    strip_space(v);
		    if (!v.empty())
                        m_children.push_back(child);
		}
		else
		{
                    m_children.push_back(child);
		}

		more_values = read_multiple_values && read_struct_next(value);
	    }

	    if (background(value.length()))
	    {
		init(parent, depth, value);
		return;
	    }
	}
	
	if (parent != nullptr && parent->type() == STLList)
        {
            read_struct_end(value);
        }
	else if (m_type == List && !value.empty())
	{
	    // Add remaining value as text
            m_children.push_back(parse_child(depth, value, ""));
	}

	if (found_struct_begin)
	{
	    // Skip the remainder
	    read_struct_end(value);
	}

	// Expand only if at top-level.
        m_expanded = (depth == 0 || nchildren() <= 1  || (depth == 1 && parent->type() == STLList));

#if LOG_CREATE_VALUES
	std::clog << mytype << " "
		  << quote(myfull_name)
		  << " has " << nchildren() << " members\n";
#endif

	perl_type = '%';
	break;
    }

    case Reference:
    {
        m_expanded = true;

	int sep = value.index('@');
	sep = value.index(':', sep);

	string ref = value.before(sep);
	value = value.after(sep);

	string addr = gdb->address_expr(m_full_name);

        m_children.push_back(parse_child(depth, ref, addr, m_full_name, Pointer));
        m_children.push_back(parse_child(depth, value, m_full_name));

	if (background(value.length()))
	{
	    init(parent, depth, value);
	    return;
	}

	perl_type = '$';	// No such thing in Perl...
	break;
    }

    case STLVector:
    {
        m_expanded = true;

	int sep = value.index('=');
        if (sep>0)
        {
            string para = value.before(sep);
            if (para.contains("length 0,"))
            {
                int sep =  value.index(',');
                sep = value.index(',', sep+1);
                para = value.before(sep);
                value = value.after(sep);
                string emptyvalue = " ";
                m_children.push_back(parse_child(depth, para, m_full_name, Text));
                m_children.push_back(parse_child(depth, emptyvalue, m_full_name, Text));
            }
            else
            {
                value = value.after(sep);
                m_children.push_back(parse_child(depth, para, m_full_name, Text));
                m_children.push_back(parse_child(depth, value, m_full_name, Array));
            }
        }
        else
        {
            string emptyvalue = " ";
            m_children.push_back(parse_child(depth, value, m_full_name, Text));
            m_children.push_back(parse_child(depth, emptyvalue, m_full_name, Text));
            
        }

	if (background(value.length()))
	{
	    init(parent, depth, value);
	    return;
	}

	perl_type = '$';	// No such thing in Perl...
	break;
    }

    case STLList:
    {
        m_expanded = true;

	int sep = value.index('=');

	string para = value.before(sep);
	value = value.after(sep);

        // remove opening brackets
	sep = value.index('{');
	value = value.after(sep);

        m_children.push_back(parse_child(depth, para, m_full_name, Text));
        m_children.push_back(parse_child(depth, value, m_full_name, List));

	if (background(value.length()))
	{
	    init(parent, depth, value);
	    return;
	}

	perl_type = '$';	// No such thing in Perl...
	break;
    }

    case Sequence:
    case UnknownType:
	assert(0);
	abort();
    }

    // Handle trailing stuff (`sequences')
    if (parent == 0 || parent->type() != Sequence)
    {
	bool need_clear = true;
	while (sequence_pending(value, parent))
	{
	    if (need_clear)
	    {
#if LOG_CREATE_VALUES
		std::clog << "Sequence detected at " << quote(value) << "\n";
#endif

		clear();
		value = initial_value;

                m_type = Sequence;

#if LOG_CREATE_VALUES
		std::clog << mytype << " " << quote(myfull_name) << "\n";
#endif

		need_clear = false;
	    }
	    
	    const char *old_value = value.chars();

	    DispValue *dv = parse_child(depth, value, m_full_name);

	    if (value == old_value)
	    {
		// Nothing consumed - stop here
		dv->unlink();
		break;
	    }
	    else if (dv->type() == Simple && dv->value().empty())
	    {
		// Empty value - ignore
		dv->unlink();
	    }
	    else
	    {
                m_children.push_back(dv);
	    }
	}

#if LOG_CREATE_VALUES
	if (!need_clear)
	{
	    std::clog << mytype << " "
		      << quote(myfull_name)
		      << " has " << nchildren() << " members\n";
	}
#endif
    }

    if (gdb->program_language() == LANGUAGE_PERL && is_perl_prefix(perl_type))
    {
	// Set new type
	if (!m_full_name.empty() && is_perl_prefix(m_full_name[0]))
            m_full_name[0] = perl_type;
    }

    background(value.length());
    m_changed = true;
}

// Destructor helper
void DispValue::clear()
{
    for (int i = 0; i < nchildren(); i++)
	child(i)->unlink();

    m_children.clear();

    if (plotter() != 0)
    {
	plotter()->terminate();
        m_plotter = 0;
    }

    clear_cached_box();
}

//-----------------------------------------------------------------------------
// Cache
//-----------------------------------------------------------------------------

void DispValue::validate_box_cache()
{
    int i;
    for (i = 0; i < nchildren(); i++)
	child(i)->validate_box_cache();

    for (i = 0; i < nchildren(); i++)
    {
	if (child(i)->cached_box() == 0 ||
	    child(i)->m_cached_box_change > m_cached_box_change)
	{
	    clear_cached_box();
	    break;
	}
    }
}

// Clear box caches for this and all children
void DispValue::clear_box_cache()
{
    clear_cached_box();

    for (int i = 0; i < nchildren(); i++)
	child(i)->clear_box_cache();
}

//-----------------------------------------------------------------------------
// Resources
//-----------------------------------------------------------------------------

// Return dereferenced name.  Only if type() == Pointer.
string DispValue::dereferenced_name() const
{
    switch (m_type)
    {
    case Pointer:
    {
	string f = full_name();
	if (f.contains('/', 0))
	    f = f.from(2);	// Skip /FMT expressions

	return deref(f);
    }

    case Simple:
    case Text:
    case Array:
    case Sequence:
    case List:
    case Struct:
    case Reference:
    case UserCommand:
    case STLVector:
    case STLList:
	return "";

    case UnknownType:
	assert(0);
	abort();
    }

    return "";
}


//-----------------------------------------------------------------------------
// Modifiers
//-----------------------------------------------------------------------------

// Expand.  Like expand(), but expand entire subtree
void DispValue::expandAll(int depth)
{
    if (depth == 0)
	return;

    _expand();

    for (int i = 0; i < nchildren(); i++)
    {
	child(i)->expandAll(depth - 1);
    }
}

// Collapse.  Like collapse(), but collapse entire subtree
void DispValue::collapseAll(int depth)
{
    if (depth == 0)
	return;

    _collapse();

    for (int i = 0; i < nchildren(); i++)
    {
	child(i)->collapseAll(depth - 1);
    }
}

// Count expanded nodes in tree
int DispValue::expandedAll() const
{
    int count = 0;
    if (expanded())
	count++;
    for (int i = 0; i < nchildren(); i++)
	count += child(i)->expandedAll();

    return count;
}

// Count collapsed nodes in tree
int DispValue::collapsedAll() const
{
    int count = 0;
    if (collapsed())
	count++;
    for (int i = 0; i < nchildren(); i++)
	count += child(i)->collapsedAll();

    return count;
}


// Return height of entire tree
int DispValue::height() const
{
    int d = 0;

    for (int i = 0; i < nchildren(); i++)
	d = max(d, child(i)->height());

    return d + 1;
}

// Return height of expanded tree
int DispValue::heightExpanded() const
{
    if (collapsed())
	return 0;

    int d = 0;

    for (int i = 0; i < nchildren(); i++)
    {
	if (child(i)->collapsed())
	    return 1;

	d = max(d, child(i)->heightExpanded());
    }

    return d + 1;
}

void DispValue::set_orientation(DispValueOrientation orientation)
{
    if (m_orientation == orientation)
	return;

    m_orientation = orientation;
    clear_cached_box();

    if (type() == Simple && plotter() != 0)
	plot();

    // Save orientation for next time
    switch (type())
    {
    case Array:
	app_data.array_orientation = orientation;
	break;

    case List:
    case Struct:
	app_data.struct_orientation = orientation;
	break;

    default:
	break;
    }
}

void DispValue::set_member_names(bool value)
{
    if (m_member_names == value)
	return;

    m_member_names = value;
    clear_cached_box();

    // Save setting for next time
    app_data.show_member_names = value;
}


//-----------------------------------------------------------------------------
// Update values
//-----------------------------------------------------------------------------

// Update values from VALUE.  Set WAS_CHANGED iff value changed; Set
// WAS_INITIALIZED iff type changed.  If TYPE is given, use TYPE as
// type instead of inferring it.  Note: THIS can no more be referenced
// after calling this function; use the returned value instead.
DispValue *DispValue::update(string& value, 
			     bool& was_changed, bool& was_initialized,
			     DispValueType given_type)
{
    DispValue *source = parse(0, 0, value, 
			      full_name(), name(), given_type);

    if (background(value.length()))
    {
	// Aborted while parsing - use SOURCE instead of original
	DispValue *ret = source->link();
	ret->m_changed = was_changed = was_initialized = true;

	// Have the new DispValue take over the plotter
	if (ret->plotter() == 0)
	{
	    ret->m_plotter = plotter();
            m_plotter = 0;
	}

	unlink();
	return ret;
    }

    DispValue *dv = update(source, was_changed, was_initialized);

    if (was_changed || was_initialized)
	dv->clear_cached_box();

    source->unlink();

    return dv;
}


// Update values from SOURCE.  Set WAS_CHANGED iff value changed; Set
// WAS_INITIALIZED iff type changed.  Note: Neither THIS nor SOURCE
// can be referenced after calling this function; use the returned
// value instead.
DispValue *DispValue::update(DispValue *source, 
			     bool& was_changed, bool& was_initialized)
{
    assert(source->OK());

    bool was_plotted = (plotter() != 0);

    DispValue *dv = _update(source, was_changed, was_initialized);
    assert(dv->OK());

    if (was_plotted && was_changed)
	dv->plot();

    return dv;
}

DispValue *DispValue::_update(DispValue *source, 
			      bool& was_changed, bool& was_initialized)
{
    if (source == this)
    {
	// We're updated from ourselves -- ignore it all.  
	// This happens when a cluster is updated from the values of
	// the clustered dislays.
	if (descendant_changed())
	    was_changed = true;

	return this;
    }

    if (m_changed)
    {
	// Clear `changed' flag
        m_changed = false;
	was_changed = true;
    }

    if (source->enabled() != enabled())
    {
        m_enabled = source->enabled();
	was_changed = true;

	// We don't set CHANGED to true since enabled/disabled changes
	// are merely a change in the view, not a change in the data.
    }

    if (source->full_name() == full_name() && source->type() == type())
    {
	switch (type())
	{
	case Simple:
	case Text:
	case Pointer:
        case UserCommand:
	    // Atomic values
	    if (m_value != source->value())
	    {
                m_value = source->value();
                m_changed = was_changed = true;
	    }
	    return this;

	case Array:
	    // Array.  Check for 1st element, too.
	    if (m_have_index_base != source->m_have_index_base &&
		(m_have_index_base && m_index_base != source->m_index_base))
		break;

	    // FALL THROUGH
	case Reference:
	case Sequence:
        case STLVector:
        case STLList:
	    // Numbered children.  If size changed, we assume
	    // the whole has been changed.
	    if (nchildren() == source->nchildren())
	    {
		for (int i = 0; i < nchildren(); i++)
		{
		    // Update each child
                    m_children[i] = child(i)->update(source->child(i),
						    was_changed,
						    was_initialized);
		}
		return this;
	    }
	    break;

	case List:
	case Struct:
	{
	    // Named children.  Check whether names are the same.
	    bool same_members = (nchildren() == source->nchildren());

	    for (int i = 0; same_members && i < nchildren(); i++)
	    {
		if (child(i)->full_name() != source->child(i)->full_name())
		    same_members = false;
	    }

	    if (same_members)
	    {
		// Update each child
		for (int i = 0; i < nchildren(); i++)
		{
                    m_children[i] = child(i)->update(source->child(i),
						    was_changed,
						    was_initialized);
		}
		return this;
	    }

	    // Members have changed.
	    // Be sure to mark only those members that actually have changed
	    // (i.e. don't mark the entire struct and don't mark new members)
	    // We do so by creating a new list of children.  `Old' children
	    // that still are reported get updated; `new' children are added.
	    std::vector<DispValue *> new_children;
	    std::vector<DispValue *> processed_children;
	    for (int j = 0; j < source->nchildren(); j++)
	    {
		DispValue *c = 0;
		for (int i = 0; c == 0 && i < nchildren(); i++)
		{
		    bool processed = false;
		    for (int k = 0; k < int(processed_children.size()); k++)
		    {
			if (child(i) == processed_children[k])
			    processed = true;
		    }
		    if (processed)
			continue;

		    if (child(i)->full_name() == source->child(j)->full_name())
		    {
			c = child(i)->update(source->child(j),
					     was_changed,
					     was_initialized);
			processed_children.push_back(child(i));
		    }
		}

		if (c == 0)
		{
		    // Child not found -- use source child instead
		    c = source->child(j)->link();
		}

		new_children.push_back(c);
	    }
            m_children = new_children;
	    was_changed = was_initialized = true;
	    return this;
	}

	case UnknownType:
	    assert(0);
	    abort();
	}
    }

    // Type, name or structure have changed -- use SOURCE instead of original
    DispValue *ret = source->link();
    ret->m_changed = was_changed = was_initialized = true;

    // Copy the basic settings
    ret->m_expanded = expanded();
    ret->dereference(dereferenced());
    ret->set_orientation(orientation());
    ret->set_member_names(member_names());

    // Have new DispValue take over the plotter
    if (ret->plotter() == 0)
    {
	ret->m_plotter = plotter();
        m_plotter = 0;
    }

    unlink();
    return ret;
}

// Return true iff this or some descendant changed
bool DispValue::descendant_changed() const
{
    if (m_changed)
	return true;

    for (int i = 0; i < nchildren(); i++)
	if (child(i)->descendant_changed())
	    return true;

    return false;
}

//-----------------------------------------------------------------------------
// Find descendant
//-----------------------------------------------------------------------------

// Return true iff SOURCE and this are structurally equal.
// If SOURCE_DESCENDANT (a descendant of SOURCE) is set, 
// return its equivalent descendant of this in DESCENDANT.
bool DispValue::structurally_equal(const DispValue *source,
				   const DispValue *source_descendant,
				   const DispValue *&descendant) const
{
    if (source == source_descendant)
	descendant = this;

    if (type() != source->type())
	return false;		// Differing type

    switch (type())
    {
	case Simple:
	case Text:
	case Pointer:
        case UserCommand:
	    return true;	// Structurally equal
		
	case Array:
	{
	    if (nchildren() != source->nchildren())
		return false;	// Differing size

	    if (m_have_index_base != source->m_have_index_base)
		return false;	// Differing base

	    if (m_have_index_base && m_index_base != source->m_index_base)
		return false;	// Differing base

	    for (int i = 0; i < nchildren(); i++)
	    {
		DispValue *child = m_children[i];
		DispValue *source_child = source->child(i);
		bool eq = child->structurally_equal(source_child, 
						    source_descendant,
						    descendant);

		if (!eq)
		    return false;
	    }
	    return true;	// All children structurally equal
	}

	case List:
	case Struct:
	case Sequence:
	case Reference:
        case STLVector:
        case STLList:
	{
	    if (nchildren() != source->nchildren())
		return false;

	    for (int i = 0; i < nchildren(); i++)
	    {
		DispValue *child = m_children[i];
		DispValue *source_child = source->child(i);
		bool eq = child->structurally_equal(source_child, 
						    source_descendant,
						    descendant);

		if (!eq)
		    return false;
	    }
	    return true;	// All children structurally equal
	}

	case UnknownType:
	    assert(0);
	    abort();
    }

    return false;		// Not found
}

//-----------------------------------------------------------------------------
// Plotting
//-----------------------------------------------------------------------------


bool DispValue::can_plot() const
{
    if (can_plotImage() || can_plotCVMat())
        return true;

    if (can_plot3d())
        return true;

    if (can_plotVector())
        return true;

    if (can_plot2d())
        return true;

    if (can_plot1d())
        return true;

    // Search for plottable array children
    for (int i = 0; i < nchildren(); i++)
        if (child(i)->can_plot())
            return true;

    return false;
}

bool DispValue::starts_number(char c)
{
    return c == '.' || c == '+' || c == '-' || isdigit(c);
}

bool DispValue::can_plot1d() const
{
    if (type() != Simple)
	return false;

    const string& v = value();
    if (v.length() == 0)
	return false;	// Empty value
    if (!starts_number(v[0]))
	return false;	// Not a numeric value

    return true;
}

// If the names of all children have the form (PREFIX)(INDEX)(SUFFIX),
// return the common PREFIX and SUFFIX.
void DispValue::get_index_surroundings(string& prefix, string& suffix) const
{
    assert (nchildren() > 0);

    prefix = child(0)->full_name();
    suffix = child(0)->full_name();

    for (int i = 1; i < nchildren(); i++)
    {
	prefix = common_prefix(prefix, child(i)->full_name());
	suffix = common_suffix(suffix, child(i)->full_name());
    }
}

// If the name has the form (PREFIX)(INDEX)(SUFFIX), return INDEX
string DispValue::index(const string& prefix, const string& suffix) const
{
    string idx = full_name();
    idx = idx.from(int(prefix.length()));
    idx = idx.before(int(idx.length() - suffix.length()));
    strip_space(idx);

    return idx;
}

bool DispValue::can_plot2d() const
{
    if (type() == Array)
    {
	for (int i = 0; i < nchildren(); i++)
	{
	    if (!child(i)->can_plot1d())
		return false;
	}

	return true;
    }

    if (nchildren() > 0)
    {
	// If we have a list of indexed names, then we can plot in 2d.
	int i;
	string prefix, suffix;
	get_index_surroundings(prefix, suffix);
	
	for (i = 0; i < nchildren(); i++)
	{
	    string idx = child(i)->index(prefix, suffix);
	    if (!idx.matches(rxdouble) && !idx.matches(rxint))
		return false;
	}

	for (i = 0; i < nchildren(); i++)
	{
	    if (!child(i)->can_plot1d())
		return false;
	}

	return true;
    }

    return false;
}

bool DispValue::can_plot3d() const
{
    if (type() != Array)
	return false;

    int grandchildren = -1;
    for (int i = 0; i < nchildren(); i++)
    {
	if (!child(i)->can_plot2d())
	    return false;

	if (i == 0)
	    grandchildren = child(i)->nchildren_with_repeats();
	else if (child(i)->nchildren_with_repeats() != grandchildren)
	    return false;	// Differing number of grandchildren
    }

    return true;
}

bool DispValue::can_plotImage() const
{
    if (m_type!=Struct)
        return false;

    if (std::none_of(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "pixmap"; }))
        return false;

    if (std::none_of(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "cdim"; }))
        return false;

    if (std::none_of(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "xdim"; }))
        return false;

    if (std::none_of(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "ydim"; }))
        return false;

    return true;
}

bool DispValue::can_plotVector() const
{
    if (m_type!=STLVector)
        return false;

    // find one child with plotable data
    bool canplot = true;
    for (int i = 0; i < nchildren(); i++)
    {
        canplot = true;
        DispValue *child = m_children[i];
        for (int j=0; j < child->nchildren(); j++)
        {
            if (child->m_children[j]->can_plot1d())
            {
                canplot = false;
                break;
            }
        }
        if (canplot)
            break;
    }

    return canplot;
}

bool DispValue::can_plotCVMat() const
{
    if (m_type!=Struct)
        return false;

    if (std::none_of(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "flags"; }))
        return false;

    if (std::none_of(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "data"; }))
        return false;

    if (std::none_of(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "dims"; }))
        return false;

    if (std::none_of(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "cols"; }))
        return false;

    if (std::none_of(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "rows"; }))
        return false;

    if (std::none_of(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "datastart"; }))
        return false;

    if (std::none_of(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "dataend"; }))
        return false;

    return true;
}

int DispValue::nchildren_with_repeats() const
{
    int sum = 0;
    for (int i = 0; i < nchildren(); i++)
	sum += child(i)->repeats();
    return sum;
}

// Return a title for NAME
string DispValue::make_title(const string& name)
{
    if (!is_user_command(name))
	return name;

    string title = user_command(name);

    if (title.contains(CLUSTER_COMMAND " ", 0))
	return title.after(CLUSTER_COMMAND " ");

    if (title.contains("graph ", 0))
	title = title.after("graph ");
    else if (title.contains("info ", 0))
	title = title.after("info ");
    else if (title.contains(" "))
	title = title.before(" ");

    if (title.length() > 0)
	title = toupper(title[0]) + title.after(0);

    return title;
}

void DispValue::plot() const
{
    if (can_plot() == false)
	return;

    if (plotter() == 0)
    {
	string title = make_title(full_name());
	MUTABLE_THIS(DispValue *)->m_plotter = new_plotter(title, CONST_CAST(DispValue *,this));
	if (plotter() == 0)
	    return;

	plotter()->addHandler(Died, PlotterDiedHP, (void *)this);
    }

    plotter()->plot_2d_settings = app_data.plot_2d_settings;
    plotter()->plot_3d_settings = app_data.plot_3d_settings;

    bool res = _plot(plotter());

    if (res==false)
    {
        delete_plotter(plotter());
        MUTABLE_THIS(DispValue *)->m_plotter = nullptr;
        return;
    }

    plotter()->flush();
}

bool DispValue::_plot(PlotAgent *plotter) const
{
    if (can_plotImage())
        return plotImage(plotter);

    if (can_plotCVMat())
        return plotCVMat(plotter);

    if (can_plot3d())
        return plot3d(plotter);

    if (can_plotVector())
	return plotVector(plotter);

    if (can_plot2d())
        return plot2d(plotter);

    if (can_plot1d())
        return plot1d(plotter);

    // Plot all array children into one window
    for (int i = 0; i < nchildren(); i++)
	child(i)->_plot(plotter);

    return true;
}

void DispValue::replot() const
{
    if (plotter() != 0)
	plot();

    for (int i = 0; i < nchildren(); i++)
	child(i)->replot();
}

string DispValue::num_value() const
{
    const string& v = value();
    if (v.contains(rxdouble, 0))
	return v.through(rxdouble);

    if (v.contains(rxint, 0))
	return v.through(rxint);

    return "0";			// Illegal value
}


bool DispValue::plot1d(PlotAgent *plotter) const
{
    PlotElement &eldata = plotter->start_plot(make_title(full_name()));
    eldata.plottype = PlotElement::DATA_1D;
    plotter->open_stream(eldata);

    string val = num_value();

    eldata.value = num_value();
    plotter->close_stream();

    return true;
}

bool DispValue::plot2d(PlotAgent *plotter) const
{
    if (type() == Array)
    {
        if (gdb->program_language()== LANGUAGE_C)
        {
            PlotElement &eldata = plotter->start_plot(make_title(full_name()));
            eldata.plottype = PlotElement::DATA_2D;

            // get variable type and dimensions of array
            string gdbtype;
            string answer = gdb_question("whatis " + m_full_name);
            gdbtype = answer.after("=");
            strip_space(gdbtype);
            string length = (gdbtype.after('['));
            length = length.before(']');
            gdbtype = gdbtype.before('[');
            strip_space(gdbtype);

            // get starting address
            answer = gdb_question("print /x  &" + m_full_name + "[0] ");
            string address = answer.after("=");
            strip_space(address);

            // get size of variable type
            answer = gdb_question("print sizeof(" + gdbtype + ")");
            string sizestr = answer.after("=");
            strip_space(sizestr);

            // write memory block to file
            string question = "dump binary memory " + eldata.file + " " + address + " " + address + "+" + length + "*" + sizestr;
            answer = gdb_question(question);
            if (answer.contains("Cannot") || answer.contains("Invalid"))
            {
                set_status(answer);
                return false;
            }

            eldata.gdbtype = gdbtype;
            eldata.xdim = length;
            eldata.binary = true;
        }
        else
        {
            PlotElement &eldata  = plotter->start_plot(make_title(full_name()));
            eldata.plottype = PlotElement::DATA_2D;
            plotter->open_stream(eldata);

            int index;
            if (m_have_index_base)
                index = m_index_base;
            else
                index = gdb->default_index_base();

            for (int i = 0; i < nchildren(); i++)
            {
                DispValue *c = child(i);
                for (int ii = 0; ii < c->repeats(); ii++)
                {
                    plotter->add_point(index++, c->num_value());
                }
            }

            plotter->close_stream();
        }
    }
    else
    {
	string prefix, suffix;
	get_index_surroundings(prefix, suffix);

	PlotElement &eldata = plotter->start_plot(prefix + "x" + suffix);
        eldata.plottype = PlotElement::DATA_2D;
        plotter->open_stream(eldata);

	for (int i = 0; i < nchildren(); i++)
	{
	    DispValue *c = child(i);
	    string idx = c->index(prefix, suffix);
	    plotter->add_point(atof(idx.chars()), c->num_value());
	}

        plotter->close_stream();
    }

    return true;
}

bool DispValue::plot3d(PlotAgent *plotter) const
{
    PlotElement &eldata = plotter->start_plot(make_title(full_name()));
    eldata.plottype = PlotElement::DATA_3D;
    if (gdb->program_language()== LANGUAGE_C)
    {
        // get variable type and dimensions of array
        string gdbtype;
        string answer = gdb_question("whatis " + m_full_name);
        gdbtype = answer.after("=");
        strip_space(gdbtype);
        string ydim = gdbtype.after('[');
        string xdim = ydim.after('[');
        ydim = ydim.before(']');
        xdim = xdim.before(']');
        gdbtype = gdbtype.before('[');
        strip_space(gdbtype);

        // get starting address
        answer = gdb_question("print /x  &" + m_full_name + "[0] ");
        string address = answer.after("=");
        strip_space(address);

        // get size of variable type
        answer = gdb_question("print sizeof(" + gdbtype + ")");
        string sizestr = answer.after("=");
        strip_space(sizestr);

        // write memory block to file
        string question = "dump binary memory " + eldata.file + " " + address + " " + address + "+" + ydim + "*" + xdim + "*"  + sizestr;
        answer = gdb_question(question);
        if (answer.contains("Cannot") || answer.contains("Invalid"))
        {
            set_status(answer);
            return false;
        }

        eldata.xdim = xdim;
        eldata.ydim = ydim;
        eldata.gdbtype = gdbtype;
        eldata.binary = true;
    }
    else
    {
        plotter->open_stream(eldata);

        int index;
        if (m_have_index_base)
            index = m_index_base;
        else
            index = gdb->default_index_base();

        for (int i = 0; i < nchildren(); i++)
        {
            DispValue *c = child(i);
            int c_index;
            if (c->m_have_index_base)
                c_index = c->m_index_base;
            else
                c_index = gdb->default_index_base();

            for (int ii = 0; ii < c->repeats(); ii++)
            {
                for (int j = 0; j < c->nchildren(); j++)
                {
                    DispValue *cc = c->child(j);
                    for (int jj = 0; jj < cc->repeats(); jj++)
                        plotter->add_point(index, c_index++, cc->num_value());
                }

                index++;
            }

            plotter->add_break();
        }

        plotter->close_stream();
    }

    return true;
}

bool DispValue::plotVector(PlotAgent *plotter) const
{
    PlotElement &eldata = plotter->start_plot(make_title(full_name()));
    eldata.plottype = PlotElement::DATA_2D;

    // get variable type
    string gdbtype;
    string answer = gdb_question("whatis " + m_full_name + "[0]");
    gdbtype = answer.after("=");
    strip_space(gdbtype);

    // get size of variable type
    answer = gdb_question("print sizeof(" + gdbtype + ")");
    string sizestr = answer.after("=");
    strip_space(sizestr);

    // get starting address
    answer = gdb_question("print /x  &" + m_full_name + "[0] ");
    string address = answer.after("=");
    strip_space(address);

    // get length of vector
    answer = gdb_question("print " + m_full_name + ".size()");
    string length = answer.after("=");
    strip_space(length);

    // write memory block to file
    string question = "dump binary memory " + eldata.file + " " + address + " " + address + "+" + length + "*" + sizestr;
    answer = gdb_question(question);
    if (answer.contains("Cannot") || answer.contains("Invalid"))
    {
        set_status(answer);
        return false;
    }

    eldata.xdim = length;
    eldata.gdbtype = gdbtype;
    eldata.binary = true;

    return true;
}

bool DispValue::plotImage(PlotAgent *plotter) const
{
    auto child = std::find_if(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "cdim"; });
    if (child == m_children.end())
        return false;

    string cdimstr = (*child)->value();
    int cdim = atoi(cdimstr.chars());

    if (cdim!=1 && cdim!=3)
        return false; 

    PlotElement &eldata = plotter->start_plot(make_title(full_name()));
    eldata.plottype = PlotElement::IMAGE;

    child = std::find_if(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "pixmap"; });
    if (child == m_children.end())
        return false;

    string address  = (*child)->value();
    int pos = address.index(rxwhite);
    if (pos>0)
        address = address.before(pos);

    child = std::find_if(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "xdim"; });
    if (child == m_children.end())
        return false;

    string xdimstr = (*child)->value().chars();

    child = std::find_if(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "ydim"; });
    if (child == m_children.end())
        return false;

    string ydimstr =(*child)->value().chars();

    string answer = gdb_question("whatis (" + m_full_name + ").pixmap[0]");
    string gdbtype = answer.after("=");
    strip_space(gdbtype);

    answer = gdb_question("print sizeof(" + gdbtype + ")");
    string sizestr = answer.after("=");
    strip_space(sizestr);

    string question = "dump binary memory " + eldata.file + " " + address + " " + address + "+" + xdimstr + "*" + ydimstr + "*" + cdimstr + "*" + sizestr;
    answer = gdb_question(question);
    if (answer.contains("Cannot") || answer.contains("Invalid"))
    {
        set_status(answer);
        return false;
    }

    eldata.xdim = xdimstr;
    eldata.ydim = ydimstr;
    eldata.gdbtype = gdbtype;
    eldata.binary = true;

    if (cdim==3)
    {
        eldata.plottype = PlotElement::RGBIMAGE;
        int size = atoi(sizestr.chars());
        int xdim  = atoi(xdimstr.chars());
        int ydim  = atoi(ydimstr.chars());
        int cdim  = atoi(cdimstr.chars());
        int num = xdim * ydim * cdim;

        char *filebuffer = new char[size*num];
        FILE *fp = fopen(eldata.file.chars(), "rb");
        int read = fread(filebuffer, size, num, fp);
        fclose(fp);

        if (read!=num)
        {
            delete [] filebuffer;
            return false;
        }

        fp = fopen(eldata.file.chars(), "wb");
        char *red = &filebuffer[0];
        char *green = &filebuffer[xdim*ydim*size];
        char *blue = &filebuffer[xdim*ydim*size*2];
        for (int y=0; y<ydim; y++)
        {
            for (int x=0; x<xdim; x++)
            {
                fwrite(red, size, 1, fp);
                red += size;
                fwrite(green, size, 1, fp);
                green += size;
                fwrite(blue, size, 1, fp);
                blue += size;
            }
        }
        fclose(fp);
        delete [] filebuffer;
    }

    return true;
}

bool DispValue::plotCVMat(PlotAgent *plotter) const
{
    auto child = std::find_if(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "dims"; });
    if (child == m_children.end())
        return false;

    string cdimstr = (*child)->value();
    int cdim = atoi(cdimstr.chars());

    if (cdim!=2)
        return false; // only 2 dimensional images

    child = std::find_if(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "flags"; });
    if (child == m_children.end())
        return false;

    int flags = atoi((*child)->value().chars());
    if (flags>>16 != 0x42FF)
        return false;

    int colorchannels =((flags &0xfff) >> 3) + 1;
    if (colorchannels != 1 && colorchannels!=3)
        return false;

    string gdbtype;
    switch (flags & 0x0007)
    {
        case 0: // CV_8U
            gdbtype = "unsigned char";
            break;
        case 1: // CV_8S
            gdbtype = "char";
            break;
        case 2: // CV_16U
            gdbtype = "unsigned short";
            break;
        case 3: // CV_16S
            gdbtype = "short";
            break;
        case 4: // CV_32S
            gdbtype = "int";
            break;
        case 5: // CV_32F
            gdbtype = "float";
            break;
        case 6: // CV_64F
            gdbtype = "double";
            break;
        default:
            return false;
    }

    PlotElement &eldata = plotter->start_plot(make_title(full_name()));
    eldata.plottype = PlotElement::IMAGE;

    child = std::find_if(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "data"; });
    if (child == m_children.end())
        return false;

    string startaddress  = (*child)->value();
    int pos = startaddress.index(rxwhite);
    if (pos>0)
        startaddress = startaddress.before(pos);

    child = std::find_if(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "datalimit"; });
    if (child == m_children.end())
        return false;

    string endaddress  = (*child)->value();
    pos = endaddress.index(rxwhite);
    if (pos>0)
        endaddress = endaddress.before(pos);

    child = std::find_if(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "cols"; });
    if (child == m_children.end())
        return false;

    string colsstr = (*child)->value();

    child = std::find_if(m_children.begin(), m_children.end(), [&](const DispValue *child) { return child->m_print_name == "rows"; });
    if (child == m_children.end())
        return false;

    string rowsstr = (*child)->value();


    string question = "dump binary memory " + eldata.file + " " + startaddress + " " + endaddress;
    string answer = gdb_question(question);
    if (answer.contains("Cannot") || answer.contains("Invalid"))
    {
        set_status(answer);
        return false;
    }

    if (colorchannels==3)
        eldata.plottype = PlotElement::BGRIMAGE;
    else
        eldata.plottype = PlotElement::IMAGE;

    eldata.xdim = colsstr;
    eldata.ydim = rowsstr;
    eldata.gdbtype = gdbtype;
    eldata.binary = true;

    return true;
}

void DispValue::PlotterDiedHP(Agent *source, void *client_data, void *)
{
    (void) source;		// Use it

    DispValue *dv = (DispValue *)client_data;

    PlotAgent *agent = dv->m_plotter;
//    assert(source == dv->plotter());

//     dv->plotter()->removeHandler(Died, PlotterDiedHP, (void *)dv);
    agent->removeHandler(Died, PlotterDiedHP, (void *)dv);
    dv->m_plotter = 0;
}

// Print plots to FILENAME
void DispValue::print_plots(const string& filename, 
			    const PrintGC& gc) const
{
    // Print self
    if (plotter() != 0)
	plotter()->print(filename, gc);

    // Print children
    for (int i = 0; i < nchildren(); i++)
	child(i)->print_plots(filename, gc);
}


// Show whether plot is active
void DispValue::set_plot_state(const string& state) const
{
    // Handle self
    if (plotter() != 0)
	plotter()->set_state(state);

    // Handle children
    for (int i = 0; i < nchildren(); i++)
	child(i)->set_plot_state(state);
}


//-----------------------------------------------------------------------------
// Background processing
//-----------------------------------------------------------------------------

static bool nop(int) { return false; }

bool (*DispValue::background)(int processed) = nop;



//-----------------------------------------------------------------------------
// Debugging
//-----------------------------------------------------------------------------

bool DispValue::OK() const
{
    assert (m_links > 0);
    assert (m_cached_box == 0 || m_cached_box->OK());

    for (int i = 0; i < nchildren(); i++)
	assert(child(i)->OK());

    return true;
}
