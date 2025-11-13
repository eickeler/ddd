// $Id$
// Read and store type and value of a displayed expression

// Copyright (C) 1995 Technische Universitaet Braunschweig, Germany.
// Written by Dorothea Luetkehaus <luetke@ips.cs.tu-bs.de>.
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

#ifndef _DDD_DispValue_h
#define _DDD_DispValue_h

//-----------------------------------------------------------------------------
// A DispValue reads and stores type and value of a displayed expression
//-----------------------------------------------------------------------------

#include "base/strclass.h"
#include "base/bool.h"
#include "base/mutable.h"
#include "DispValueT.h"
#include "template/StringSA.h"
#include "box/Box.h"
#include <Xm/Xm.h>

#include <vector>
#include <map>


class Agent;
class PlotAgent;

typedef unsigned char DispValueOrientation;
const unsigned char Vertical   = XmVERTICAL;
const unsigned char Horizontal = XmHORIZONTAL;

class DispValue {
    // General members
    DispValueType m_type;
    bool m_expanded;
    bool m_enabled;
    string m_full_name;		// Full name
    string m_print_name;	// Name relative to parent
    string m_addr;		// Address as found
    bool m_changed;
    int m_repeats;		// Number of repetitions

    // Type-dependent members
    string m_value;		// Value of basic types
    bool m_dereferenced;	// True iff pointer is dereferenced
    bool m_member_names;	// True iff struct shows member names
    std::vector<DispValue *> m_children;	// Array or Struct members
    int m_index_base;		// First index
    bool m_have_index_base;	// True if INDEX_BASE is valid
    mutable DispValueOrientation m_orientation; // Array orientation
    mutable bool m_has_plot_orientation;   // True if plotter set the orientation

    // Plotting stuff
    mutable PlotAgent *m_plotter;	// Plotting agent

    // Caching stuff
    Box *m_cached_box;		    // Last box
    int m_cached_box_change;        // Last cached box change
    static int m_cached_box_tics;   // Counter

    // Initialize from VALUE.  If TYPE is given, use TYPE as type
    // instead of inferring it.
    void init(DispValue *parent, int depth, 
	      string& value, DispValueType type = UnknownType);

    // Delete helper
    void clear();

    // Assignment
    void assign(DispValue& dv);

    // Helpers
    static StringStringAssoc type_cache;
    static int index_base(const string& expr, int dim);
    static string add_member_name(const string& base, 
				  const string& member_name);

    // Plotting stuff
    bool getGnuplotType(string expr, string &gdbtype, string &gnuplottype, string &sizestr) const;
    bool _plot(PlotAgent *&plotter) const;
    bool plot1d(PlotAgent *&plotter) const;
    bool plot2d(PlotAgent *&plotter) const;
    bool plot3d(PlotAgent *&plotter) const;
    bool plotVector(PlotAgent *&plotter) const;
    bool plotImage(PlotAgent *&plotter) const;
    bool plotCVMat(PlotAgent *&plotter) const;
    bool can_plot1d() const;
    bool can_plot2d() const;
    bool can_plot3d() const;
    bool can_plotVector() const;
    bool can_plotImage() const;
    bool can_plotCVMat() const;
    static bool starts_number(char c);

    static void PlotterDiedHP(Agent *, void *, void *);

    // Update helper
    DispValue *_update(DispValue *source, 
		       bool& was_changed, bool& was_initialized);

    // Clear cached box
    void clear_cached_box()
    {
	if (m_cached_box != 0)
	{
            m_cached_box->unlink();
            m_cached_box = 0;
	}
        m_cached_box_change = 0;
    }

private:
    DispValue& operator = (const DispValue&);

    // If the names of all children have the form (PREFIX)(INDEX)(SUFFIX),
    // return the common PREFIX and SUFFIX.
    void get_index_surroundings(string& prefix, string& suffix) const;

    // If the name has the form (PREFIX)(INDEX)(SUFFIX), return INDEX
    string index(const string& prefix, const string& suffix) const;

protected:
    int m_links;			// #references (>= 1)

    // Array, Struct
    // Expand/collapse single value
    void _expand()
    {
	if (m_expanded)
	    return;

        m_expanded = true;
	clear_cached_box();
    }
    void _collapse()
    {
	if (!m_expanded)
	    return;

        m_expanded = false;
	clear_cached_box();
    }

    // True if more sequence members are coming
    static bool sequence_pending(const string& value, 
				 const DispValue *parent);

    // Numeric value
    string num_value() const;

    // The DispValue type and address are determined from VALUE
    DispValue (DispValue *parent, 
	       int        depth,
	       string&    value,
	       const string& full_name, 
	       const string& print_name,
	       DispValueType type = UnknownType);

    // Parsing function
    static DispValue *parse(DispValue *parent, 
			    int depth,
			    string& value,
			    const string& full_name, 
			    const string& print_name,
			    DispValueType type = UnknownType);

    DispValue *parse_child(int depth,
			   string& value,
			   const string& full_name, 
			   const string& _print_name,
			   DispValueType type = UnknownType)
    {
	return parse(this, depth + 1, value, full_name, _print_name, type);
    }

    DispValue *parse_child(int depth,
			   string& value,
			   const string& name, 
			   DispValueType type = UnknownType)
    {
	return parse_child(depth, value, name, name, type);
    }


    // Copy constructor
    DispValue (const DispValue& dv);

    // Return a `normalized' prefix BASE for arrays and structs
    string normalize_base(const string& base) const;

public:
    // Global settings
    static bool expand_repeated_values;

    // Parse VALUE into a DispValue tree
    static DispValue *parse(string& value, const string& name)
    {
	return parse(0, 0, value, name, name);
    }

    // Duplicator
    DispValue *dup() const
    {
	return new DispValue(*this);
    }

    // Destructor
    virtual ~DispValue()
    {
	assert (m_links == 0);
	clear();
    }

    // Create new reference
    DispValue *link()
    {
	assert(m_links > 0);
        m_links++;
	return this;
    }

    // Kill reference
    void unlink()
    {
	assert(m_links > 0);
	if (--m_links == 0)
	    delete this;
    }

    // General resources
    DispValueType type()       const { return m_type; }
    bool enabled()             const { return m_enabled; }
    const string& full_name()  const { return m_full_name; }
    const string& name()       const { return m_print_name; }
    const string& addr()       const { return m_addr; }
    int repeats()              const { return m_repeats; }
    bool has_plot_orientation()  const { return m_has_plot_orientation; }

    int& repeats()       { clear_cached_box(); return m_repeats; }
    string& full_name()  { clear_cached_box(); return m_full_name; }
    string& name()       { clear_cached_box(); return m_print_name; }
    bool& enabled()      { clear_cached_box(); return m_enabled; }

    bool is_changed() const { return m_changed; }
    bool descendant_changed() const;
    bool expanded()   const { return m_expanded; }
    bool collapsed()  const { return !expanded(); }

    // Return height of entire tree
    int height() const;

    // Return height of expanded tree
    int heightExpanded() const;


    // Type-specific resources

    // Simple or Pointer
    const string& value() const { return m_value; }

    // Pointer
    bool dereferenced() const { return m_dereferenced; }
    string dereferenced_name() const;

    // Struct
    bool member_names() const { return m_member_names; }
    void set_member_names(bool value);

    // Array, Struct, List, Sequence ...
    int nchildren() const { return m_children.size(); }
    DispValue *child(int i) const { return m_children[i]; }
    int nchildren_with_repeats() const;

    // General modifiers

    // Expand/collapse entire tree.  If DEPTH is non-negative, expand
    // DEPTH levels only.  If DEPTH is negative, expand all.
    void collapseAll(int depth = -1);
    void expandAll(int depth = -1);

    // Custom calls
    void collapse() { collapseAll(1); }
    void expand()   { expandAll(1); }

    // Count expanded or selected nodes in tree
    int expandedAll()  const;
    int collapsedAll() const;

    // Type-specific modifiers

    // Array
    void set_orientation(DispValueOrientation orientation);
    DispValueOrientation orientation() const { return m_orientation; }

    // Pointer
    void dereference(bool set = true)
    {
	if (m_dereferenced == set)
	    return;

        m_dereferenced = set;
	clear_cached_box();
    }

    // Updating

    // Update values from VALUE.  Set WAS_CHANGED iff value changed;
    // Set WAS_INITIALIZED iff type changed.  If TYPE is given, use
    // TYPE as type instead of inferring it.  Note: THIS can no more
    // be referenced after calling this function; use the returned
    // value instead.
    DispValue *update(string& value, bool& was_changed, bool& was_initialized,
		      DispValueType type = UnknownType);

    // Update values from SOURCE.  Set WAS_CHANGED iff value changed;
    // Set WAS_INITIALIZED iff type changed.  Note: Neither THIS nor
    // SOURCE can be referenced after calling this function; use the
    // returned value instead.
    DispValue *update(DispValue *source, 
		      bool& was_changed, bool& was_initialized);

    // Return true iff SOURCE and this are structurally equal.
    // If SOURCE_DESCENDANT (a descendant of SOURCE) is not 0,
    // return its equivalent descendant of this in DESCENDANT.
    bool structurally_equal(const DispValue *source,
			    const DispValue *source_descendant,
			    const DispValue *&descendant) const;

    // Short version
    bool structurally_equal(const DispValue *source) const
    {
	const DispValue *dummy = 0;
	return structurally_equal(source, 0, dummy);
    }

    // Plotting

    // Return 0 if we cannot plot; return number of required
    // dimensions, otherwise (1, 2, or 3)
    bool can_plot() const;

    // Plot value
    void plot() const;

    // Replot value
    void replot() const;

    // Current plot agent
    PlotAgent *plotter() const { return m_plotter; }

    // Show plot state
    void set_plot_state(const string& state = "") const;

    // Background processing.  PROCESSED is the number of characters
    // processed so far.  If this returns true, abort operation.
    static bool (*background)(int processed);

    // Clear cache of all types read so far
    static void clear_type_cache();

    // Hook for inserting previously computed DispValues
    static DispValue *(*value_hook)(string& value);

    // Box cache
    Box *cached_box() const
    {
	return m_cached_box;
    }

    // Verify if cached box is recent respective to children's caches
    void validate_box_cache();

    void set_cached_box(Box *value)
    {
	clear_cached_box();
        m_cached_box = value->link();
        m_cached_box_change = m_cached_box_tics++;
    }

    // Clear box caches for this and all children
    void clear_box_cache();

    // Print plots to FILENAME
    void print_plots(const string& filename, 
		     const PrintGC& gc = PostScriptPrintGC()) const;

    // Return a title for NAME
    static string make_title(const string& name);

    // Invariant check
    virtual bool OK() const;
};

#endif // _DDD_DispValue_h
// DON'T ADD ANYTHING BEHIND THIS #endif
