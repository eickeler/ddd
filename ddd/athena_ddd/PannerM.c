/*
 * $Xorg: Panner.c,v 1.4 2001/02/09 02:03:45 xorgcvs Exp $
 *
Copyright 1989, 1994, 1998  The Open Group

Permission to use, copy, modify, distribute, and sell this software and its
documentation for any purpose is hereby granted without fee, provided that
the above copyright notice appear in all copies and that both that
copyright notice and this permission notice appear in supporting
documentation.

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
OPEN GROUP BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

Except as contained in this notice, the name of The Open Group shall not be
used in advertising or otherwise to promote the sale, use or other dealings
in this Software without prior written authorization from The Open Group.
 *
 * Author:  Jim Fulton, MIT X Consortium
 */

/* $XFree86: xc/lib/Xaw/Panner.c,v 3.8 2001/07/25 15:04:49 dawes Exp $ */
#if HAVE_ATHENA

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif
#include <ctype.h>
#include <math.h>
#include <X11/IntrinsicP.h>
#include <X11/StringDefs.h>
#include <X11/Xos.h>
#include <X11/Xmu/Drawing.h>
#include "athena_ddd/PannerMP.h"
#include <X11/Xaw/XawInit.h>

#if defined(ISC) && __STDC__ && !defined(ISC30)
extern double atof(char *);
#else
#include <stdlib.h>			/* for atof() */
#endif


#define XawMax(a, b) ((a) > (b) ? (a) : (b))
#define XawMin(a, b) ((a) < (b) ? (a) : (b))
#define XawAbs(a)    ((a) < 0 ? -(a) : (a))

#ifndef XtWidth
#define XtWidth(w)        (((RectObj)w)->rectangle.width)
#endif
#ifndef XtHeight
#define XtHeight(w)       (((RectObj)w)->rectangle.height)
#endif

/*
 * Class Methods
 */
static void XawPannerDestroy(Widget);
static void XawPannerInitialize(Widget, Widget, ArgList, Cardinal*);
static XtGeometryResult XawPannerQueryGeometry(Widget, XtWidgetGeometry*,
					       XtWidgetGeometry*);
static void XawPannerRealize(Widget, XtValueMask*, XSetWindowAttributes*);
static void XawPannerRedisplay(Widget, XEvent*, Region);
static void XawPannerResize(Widget);
static Boolean XawPannerSetValues(Widget, Widget, Widget, ArgList, Cardinal*);
static void XawPannerSetValuesAlmost(Widget, Widget, XtWidgetGeometry*,
				     XtWidgetGeometry*);

/*
 * Prototypes
 */
static void check_knob(PannermWidget, Bool);
static void get_default_size(PannermWidget, Dimension*, Dimension*);
static Bool get_event_xy(PannermWidget, XEvent*, int*, int*);
static void move_shadow(PannermWidget);
static int parse_page_string(char*, int, int, Bool*);
static void rescale(PannermWidget);
static void reset_shadow_gc(PannermWidget);
static void reset_slider_gc(PannermWidget);
static void scale_knob(PannermWidget, Bool, Bool);

/*
 * Actions
 */
static void ActionAbort(Widget, XEvent*, String*, Cardinal*);
static void ActionMove(Widget, XEvent*, String*, Cardinal*);
static void ActionNotify(Widget, XEvent*, String*, Cardinal*);
static void ActionPage(Widget, XEvent*, String*, Cardinal*);
static void ActionStart(Widget, XEvent*, String*, Cardinal*);
static void ActionStop(Widget, XEvent*, String*, Cardinal*);

/*
 * Initialization
 */
static char defaultTranslations[] =
"<Btn1Down>:"		"start()\n"
"<Btn1Motion>:"		"move()\n"
"<Btn1Up>:"		"notify() stop()\n"
"<Btn2Down>:"		"abort()\n"
"<Key>space:"		"page(+1p,+1p)\n"
"<Key>Delete:"		"page(-1p,-1p)\n"
":<Key>KP_Delete:"	"page(-1p,-1p)\n"
"<Key>BackSpace:"	"page(-1p,-1p)\n"
"<Key>Left:"		"page(-.5p,+0)\n"
"~Shift Ctrl<Btn4Down>:"		"page(-.25p,+0)\n"
":<Key>KP_Left:"	"page(-.5p,+0)\n"
"<Key>Right:"		"page(+.5p,+0)\n"
"~Shift Ctrl<Btn5Down>:"		"page(+.25p,+0)\n"
":<Key>KP_Right:"	"page(+.5p,+0)\n"
"<Key>Up:"		"page(+0,-.5p)\n"
":<Key>KP_Up:"		"page(+0,-.5p)\n"
"~Shift ~Ctrl<Btn4Down>:"   	"page(+0,-.25p)\n"
"<Key>Down:"		"page(+0,+.5p)\n"
":<Key>KP_Down:"	"page(+0,+.5p)\n"
"~Shift ~Ctrl<Btn5Down>:"   	"page(+0,+.25p)\n"
"<Key>Home:"		"page(0,0)\n"
":<Key>KP_Home:"	"page(0,0)\n"
;

static XtActionsRec actions[] = {
  {"start",	ActionStart},		/* start tmp graphics */
  {"stop",	ActionStop},		/* stop tmp graphics */
  {"abort",	ActionAbort},		/* punt */
  {"move",	ActionMove},		/* move tmp graphics on Motion event */
  {"page",	ActionPage},		/* page around usually from keyboard */
  {"notify",	ActionNotify},		/* callback new position */
};

#define offset(field)	XtOffsetOf(PannerRec, panner.field)
static XtResource resources[] = {
    {
      XtNallowOff,
      XtCAllowOff,
      XtRBoolean,
      sizeof(Boolean),
      offset(allow_off),
      XtRImmediate,
      (XtPointer)False
    },
    {
      XtNresize,
      XtCResize,
      XtRBoolean,
      sizeof(Boolean),
      offset(resize_to_pref),
      XtRImmediate,
      (XtPointer)True
    },
    {
      XtNreportCallback,
      XtCReportCallback,
      XtRCallback,
      sizeof(XtPointer),
      offset(report_callbacks),
      XtRCallback,
      NULL
    },
    {
      XtNdefaultScale,
      XtCDefaultScale,
      XtRDimension,
      sizeof(Dimension),
      offset(default_scale),
      XtRImmediate,
      (XtPointer)PANNER_DEFAULT_SCALE
    },
    {
      XtNforeground,
      XtCForeground,
      XtRPixel,
      sizeof(Pixel),
      offset(foreground),
      XtRString,
      (XtPointer)XtDefaultBackground
    },
    {
      XtNinternalSpace,
      XtCInternalSpace,
      XtRDimension,
      sizeof(Dimension),
      offset(internal_border),
      XtRImmediate,
      (XtPointer)2
    },
    {
      XtNlineWidth,
      XtCLineWidth,
      XtRDimension,
      sizeof(Dimension),
      offset(line_width),
      XtRImmediate,
      (XtPointer)0
    },
    {
      XtNcanvasWidth,
      XtCCanvasWidth,
      XtRDimension,
      sizeof(Dimension),
      offset(canvas_width),
      XtRImmediate,
      (XtPointer)0
    },
    {
      XtNcanvasHeight,
      XtCCanvasHeight,
      XtRDimension,
      sizeof(Dimension),
      offset(canvas_height),
      XtRImmediate,
      (XtPointer)0
    },
    {
      XtNsliderX,
      XtCSliderX,
      XtRPosition,
      sizeof(Position),
      offset(slider_x),
      XtRImmediate,
      (XtPointer)0
    },
    {
      XtNsliderY,
      XtCSliderY,
      XtRPosition,
      sizeof(Position),
      offset(slider_y),
      XtRImmediate,
      (XtPointer)0
    },
    {
      XtNsliderWidth,
      XtCSliderWidth,
      XtRDimension,
      sizeof(Dimension),
      offset(slider_width),
      XtRImmediate,
      (XtPointer)0
    },
    {
      XtNsliderHeight,
      XtCSliderHeight,
      XtRDimension,
      sizeof(Dimension),
      offset(slider_height),
      XtRImmediate,
      (XtPointer)0
    },
    {
      XtNshadowColor,
      XtCShadowColor,
      XtRPixel,
      sizeof(Pixel),
      offset(shadow_color),
      XtRString,
      (XtPointer)XtDefaultForeground
    },
    {
      XtNshadowThickness,
      XtCShadowThickness,
      XtRDimension,
      sizeof(Dimension),
      offset(shadow_thickness),
      XtRImmediate,
      (XtPointer)2
    },
    {
      XtNtopShadowColor,
      XtCTopShadowColor,
      XtRPixel,
      sizeof(Pixel),
      offset(top_shadow_color),
      XtRString,
      (XtPointer)"rgb:E3/E3/E3"
    },
    {
      XtNbottmShadowColor,
      XtCBottomShadowColor,
      XtRPixel,
      sizeof(Pixel),
      offset(bottom_shadow_color),
      XtRString,
      (XtPointer)"rgb:67/67/67"
    },
};
#undef offset

#define Superclass	(&simpleClassRec)
PannerClassRec pannerClassRec = {
  /* core */
  {
    (WidgetClass)Superclass,		/* superclass */
    "Panner",				/* class_name */
    sizeof(PannerRec),			/* widget_size */
    XawInitializeWidgetSet,		/* class_initialize */
    NULL,				/* class_part_initialize */
    False,				/* class_inited */
    XawPannerInitialize,		/* initialize */
    NULL,				/* initialize_hook */
    XawPannerRealize,			/* realize */
    actions,				/* actions */
    XtNumber(actions),			/* num_actions */
    resources,				/* resources */
    XtNumber(resources),		/* num_resources */
    NULLQUARK,				/* xrm_class */
    True,				/* compress_motion */
    True,				/* compress_exposure */
    True,				/* compress_enterleave */
    False,				/* visible_interest */
    XawPannerDestroy,			/* destroy */
    XawPannerResize,			/* resize */
    XawPannerRedisplay,			/* expose */
    XawPannerSetValues,			/* set_values */
    NULL,				/* set_values_hook */
    XawPannerSetValuesAlmost,		/* set_values_almost */
    NULL,				/* get_values_hook */
    NULL,				/* accept_focus */
    XtVersion,				/* version */
    NULL,				/* callback_private */
    defaultTranslations,		/* tm_table */
    XawPannerQueryGeometry,		/* query_geometry */
    XtInheritDisplayAccelerator,	/* display_accelerator */
    NULL,				/* extension */
  },
  /* simple */
  {
    XtInheritChangeSensitive,		/* change_sensitive */
  },
  /* panner */
  {
    NULL,				/* extension */
  }
};

WidgetClass pannermWidgetClass = (WidgetClass) &pannerClassRec;

typedef enum {
  XawRAISED,
  XawSUNKEN,
  XawCHISELED,
  XawLEDGED,
  XawTACK
} XawFrameType;


// the following function is taken from Vladimir Romanovski's re-write of Xaw
void 
XawDrawFrame (Widget       gw,
	      Position     x,
	      Position     y,
	      Dimension    w,
	      Dimension    h,
	      XawFrameType frame_type,
	      Dimension    t,
	      GC           lightgc,
	      GC           darkgc)
{
  XPoint top_polygon[6];
  XPoint bottom_polygon[6];
  XPoint points[3];

  
  if (t == 0 || w == 0 || h == 0)
    return;

  if( lightgc == (GC)NULL ){
    XtWarning("XawDrawFrame: lightgc is NULL in XawDrawFrame.");
    return;
  }
    
  if( darkgc == (GC)NULL ){
    XtWarning("XawDrawFrame: darkgc is NULL in XawDrawFrame.");
    return;
  }

  if (!XtIsRealized(gw)) {
    XtWarning("XawDrawFrame: widget is not realized!!!");
    return;
  }
  
#define topPolygon(i,xx,yy)           \
  top_polygon[i].x = (short) (xx);    \
  top_polygon[i].y = (short) (yy)

#define bottomPolygon(i,xx,yy)        \
  bottom_polygon[i].x = (short) (xx); \
  bottom_polygon[i].y = (short) (yy)
  

  if (frame_type == XawTACK && t <= 2)
    frame_type = XawLEDGED;

  switch (frame_type) {

  case XawRAISED :
  case XawSUNKEN :

    topPolygon (0,x    ,y    ); bottomPolygon (0,x+w  ,y+h  ); 
    topPolygon (1,x+w  ,y    ); bottomPolygon (1,x    ,y+h  );
    topPolygon (2,x+w-t,y+t  ); bottomPolygon (2,x+t  ,y+h-t);
    topPolygon (3,x+t  ,y+t  ); bottomPolygon (3,x+w-t,y+h-t);
    topPolygon (4,x+t  ,y+h-t); bottomPolygon (4,x+w-t,y+t  );
    topPolygon (5,x    ,y+h  ); bottomPolygon (5,x+w  ,y    );
    
    if (frame_type == XawSUNKEN) 
    {
      XFillPolygon(XtDisplayOfObject(gw), XtWindowOfObject(gw), darkgc,
		   top_polygon, 6, Nonconvex, CoordModeOrigin);
      
      XFillPolygon(XtDisplayOfObject(gw), XtWindowOfObject(gw), lightgc,
		   bottom_polygon, 6, Nonconvex, CoordModeOrigin);
    } 
    else if (frame_type == XawRAISED)
    {
      XFillPolygon(XtDisplayOfObject(gw), XtWindowOfObject(gw), lightgc,
		   top_polygon, 6, Nonconvex, CoordModeOrigin);
      XFillPolygon(XtDisplayOfObject(gw), XtWindowOfObject(gw), darkgc,
		   bottom_polygon, 6, Nonconvex, CoordModeOrigin);
    }
    
    break;

  case XawTACK :

    t -= 2;

    topPolygon (0,x    ,y    ); bottomPolygon (0,x+w  ,y+h  ); 
    topPolygon (1,x+w  ,y    ); bottomPolygon (1,x    ,y+h  );
    topPolygon (2,x+w-t,y+t  ); bottomPolygon (2,x+t  ,y+h-t);
    topPolygon (3,x+t  ,y+t  ); bottomPolygon (3,x+w-t,y+h-t);
    topPolygon (4,x+t  ,y+h-t); bottomPolygon (4,x+w-t,y+t  );
    topPolygon (5,x    ,y+h  ); bottomPolygon (5,x+w  ,y    );
    
    XFillPolygon(XtDisplayOfObject(gw), XtWindowOfObject(gw), lightgc,
		 top_polygon, 6, Nonconvex, CoordModeOrigin);
    XFillPolygon(XtDisplayOfObject(gw), XtWindowOfObject(gw), darkgc,
		 bottom_polygon, 6, Nonconvex, CoordModeOrigin);
    
    points[0].x = x + t + 1;	points[0].y = y + h - t - 2;
    points[1].x = x + t + 1;	points[1].y = y + t + 1;
    points[2].x = x + w - t - 2;	points[2].y = y + t + 1;
    
    XDrawLines (XtDisplayOfObject(gw), XtWindowOfObject(gw), darkgc,
		points, 3, CoordModeOrigin);
    
 /* points[0].x = x + t + 1;	        points[0].y = y + h -t - 1;   */
    points[1].x = x + w - t - 2;	points[1].y = y + h - t - 2;
 /* points[2].x = x + w - t - 1;	points[2].y = y + t + 1;      */
    
    XDrawLines (XtDisplayOfObject(gw), XtWindowOfObject(gw), lightgc,
		points, 3, CoordModeOrigin);

    break;

  case XawLEDGED :

    XawDrawFrame(gw, x, y, w, h, XawRAISED, t/2, lightgc, darkgc);
    XawDrawFrame(gw, (Position)(x + t/2), (Position)(y + t/2),
		 (Dimension)(w - 2 * (t/2)), (Dimension)(h - 2 * (t/2)),
		 XawSUNKEN, t/2, lightgc, darkgc);
    break;

  case XawCHISELED :

    XawDrawFrame(gw, x, y, w, h, XawSUNKEN, t/2, lightgc, darkgc);
    XawDrawFrame(gw, (Position)(x + t/2),(Position)(y + t/2),
		 (Dimension)(w - 2 * (t/2)), (Dimension)(h - 2 * (t/2)),
		 XawRAISED, t/2, lightgc, darkgc);
    break;

  default :
    break;

  }

#undef topPolygon
#undef bottomPolygon
}



/*
 * Implementation
 */
static void
reset_slider_gc(PannermWidget pw)
{
    XtGCMask valuemask = GCForeground;
    XGCValues values;

    if (pw->panner.slider_gc)
	XtReleaseGC((Widget)pw, pw->panner.slider_gc);

    values.foreground = pw->panner.foreground;

    pw->panner.slider_gc = XtGetGC((Widget)pw, valuemask, &values);
}

static void reset_to_bottom_shadow_gc(PannermWidget pw)
{
    if (pw->panner.top_shadow_gc)
	XtReleaseGC((Widget)pw, pw->panner.top_shadow_gc);

    if (pw->panner.bottom_shadow_gc)
	XtReleaseGC((Widget)pw, pw->panner.bottom_shadow_gc);

    XtGCMask valuemask = GCForeground;
    XGCValues values;
    values.foreground = pw->panner.top_shadow_color;

    pw->panner.top_shadow_gc = XtGetGC((Widget)pw, valuemask, &values);

    values.foreground = pw->panner.bottom_shadow_color;

    pw->panner.bottom_shadow_gc = XtGetGC((Widget)pw, valuemask, &values);
}


static void
check_knob(PannermWidget pw, Bool knob)
{
    Position pad = 2 * (pw->panner.internal_border + pw->panner.shadow_thickness);
    Position maxx = (Position)XtWidth(pw) - pad -
		    (Position)pw->panner.knob_width;
    Position maxy = (Position)XtHeight(pw) - pad -
		    (Position)pw->panner.knob_height;
    Position *x = knob ? &pw->panner.knob_x : &pw->panner.tmp.x;
    Position *y = knob ? &pw->panner.knob_y : &pw->panner.tmp.y;

    /*
     * note that positions are already normalized (i.e. internal_border
     * has been subtracted out)
     */
    if (*x < 0)
	*x = 0;
    if (*x > maxx)
	*x = maxx;

    if (*y < 0)
	*y = 0;
    if (*y > maxy)
	*y = maxy;

    if (knob) {
	pw->panner.slider_x = (Position)((double)pw->panner.knob_x
					/ pw->panner.haspect + 0.5);
	pw->panner.slider_y = (Position)((double)pw->panner.knob_y
					/ pw->panner.vaspect + 0.5);
	pw->panner.last_x = pw->panner.last_y = PANNER_OUTOFRANGE;
    }
}

static void
move_shadow(PannermWidget pw)
{
    pw->panner.shadow_valid = False;
}

static void
scale_knob(PannermWidget pw, Bool location, Bool size)
{
    if (location) {
	pw->panner.knob_x = (Position)PANNER_HSCALE(pw, pw->panner.slider_x);
	pw->panner.knob_y = (Position)PANNER_VSCALE(pw, pw->panner.slider_y);
    }
    if (size) {
	Dimension width, height;

	if (pw->panner.slider_width < 1)
	    pw->panner.slider_width = pw->panner.canvas_width;
	if (pw->panner.slider_height < 1)
	    pw->panner.slider_height = pw->panner.canvas_height;

	width = XawMin(pw->panner.slider_width, pw->panner.canvas_width);
	height = XawMin(pw->panner.slider_height, pw->panner.canvas_height);

	pw->panner.knob_width = (Dimension)PANNER_HSCALE(pw, width);
	pw->panner.knob_height = (Dimension)PANNER_VSCALE(pw, height);
    }
    if (!pw->panner.allow_off)
	check_knob(pw, True);
}

static void
rescale(PannermWidget pw)
{
    int hpad = 2 * (pw->panner.internal_border + pw->panner.shadow_thickness);
    int vpad = hpad;

    if (pw->panner.canvas_width < 1)
	pw->panner.canvas_width = XtWidth(pw);
    if (pw->panner.canvas_height < 1)
	pw->panner.canvas_height = XtHeight(pw);

    if (XtWidth(pw) <= hpad)
	hpad = 0;
    if (XtHeight(pw) <= vpad)
	vpad = 0;

    pw->panner.haspect = ((double)XtWidth(pw) - hpad + .5)
			 / (double)pw->panner.canvas_width;
    pw->panner.vaspect = ((double)XtHeight(pw) - vpad + .5)
			 / (double)pw->panner.canvas_height;
    scale_knob(pw, True, True);
}

static void
get_default_size(PannermWidget pw, Dimension *wp, Dimension *hp)
{
    Dimension pad = 2 * (pw->panner.internal_border + pw->panner.shadow_thickness);

    *wp = PANNER_DSCALE(pw, pw->panner.canvas_width) + pad;
    *hp = PANNER_DSCALE(pw, pw->panner.canvas_height) + pad;
}

static Bool
get_event_xy(PannermWidget pw, XEvent *event, int *x, int *y)
{
    int pad = pw->panner.internal_border + pw->panner.shadow_thickness;

    switch (event->type) {
	case ButtonPress:
	case ButtonRelease:
	    *x = event->xbutton.x - pad;
	    *y = event->xbutton.y - pad;
	    return (True);
	case KeyPress:
	case KeyRelease:
	    *x = event->xkey.x - pad;
	    *y = event->xkey.y - pad;
	    return (True);
	case EnterNotify:
	case LeaveNotify:
	    *x = event->xcrossing.x - pad;
	    *y = event->xcrossing.y - pad;
	    return (True);
	case MotionNotify:
	    *x = event->xmotion.x - pad;
	    *y = event->xmotion.y - pad;
	    return (True);
    }

    return (False);
}

static int
parse_page_string(char *s, int pagesize, int canvassize, Bool *relative)
{
    char *cp;
    double val = 1.0;
    Bool rel = False;

    /*
     * syntax:    spaces [+-] number spaces [pc\0] spaces
     */
    for (; isascii(*s) && isspace(*s); s++)	/* skip white space */
	;

    if (*s == '+' || *s == '-')	{		/* deal with signs */
	rel = True;
	if (*s == '-')
	    val = -1.0;
	s++;
    }
    if (!*s) {				/* if null then return nothing */
	*relative = True;
	return (0);
    }

					/* skip over numbers */
    for (cp = s; isascii(*s) && (isdigit(*s) || *s == '.'); s++)
	;
    val *= atof(cp);

					/* skip blanks */
    for (; isascii(*s) && isspace(*s); s++)
	;

    if (*s) {				/* if units */
	switch (s[0]) {
	    case 'p':
	    case 'P':
		val *= (double)pagesize;
		break;
	    case 'c':
	    case 'C':
		val *= (double)canvassize;
		break;
	}
    }
    *relative = rel;

    return ((int)val);
}

/*ARGSUSED*/
static void
XawPannerInitialize(Widget greq, Widget gnew, ArgList args, Cardinal *num_args)
{
    PannermWidget req = (PannermWidget)greq, cnew = (PannermWidget)gnew;
    Dimension defwidth, defheight;

    if (req->panner.canvas_width < 1)
	cnew->panner.canvas_width = 1;
    if (req->panner.canvas_height < 1)
	cnew->panner.canvas_height = 1;
    if (req->panner.default_scale < 1)
	cnew->panner.default_scale = PANNER_DEFAULT_SCALE;

    get_default_size(req, &defwidth, &defheight);
    if (XtWidth(req) < 1)
	XtWidth(cnew) = defwidth;
    if (XtHeight(req) < 1)
	XtHeight(cnew) = defheight;

    cnew->panner.slider_gc = NULL;
    reset_slider_gc(cnew);		/* foreground */
    cnew->panner.top_shadow_gc = NULL;
    cnew->panner.bottom_shadow_gc = NULL;
    reset_to_bottom_shadow_gc(cnew);

    rescale(cnew);			/* does a position check */
    cnew->panner.shadow_valid = False;
    cnew->panner.tmp.doing = False;
    cnew->panner.tmp.showing = False;
}

static void
XawPannerRealize(Widget gw, XtValueMask *valuemaskp,
		 XSetWindowAttributes *attr)
{
    PannermWidget pw = (PannermWidget)gw;
    
    *valuemaskp |= CWBackPixel;
    attr->background_pixel = pw->core.background_pixel;
    *valuemaskp &= ~CWBackPixmap;

    (*pannermWidgetClass->core_class.superclass->core_class.realize)
	(gw, valuemaskp, attr);
}

static void
XawPannerDestroy(Widget gw)
{
    PannermWidget pw = (PannermWidget)gw;

    XtReleaseGC(gw, pw->panner.top_shadow_gc);
    XtReleaseGC(gw, pw->panner.bottom_shadow_gc);
    XtReleaseGC(gw, pw->panner.slider_gc);
}

static void
XawPannerResize(Widget gw)
{
    rescale((PannermWidget)gw);
}

static void
XawPannerRedisplay(Widget gw, XEvent *event, Region region)
{
    PannermWidget pw = (PannermWidget)gw;
    Display *dpy = XtDisplay(gw);
    Window w = XtWindow(gw);
    int shadow_thickness = pw->panner.shadow_thickness;
    int border = pw->panner.internal_border;
    int pad = shadow_thickness + border;
    int kx = pw->panner.knob_x + pad;
    int ky = pw->panner.knob_y + pad;

    if (Superclass->core_class.expose)
	(Superclass->core_class.expose)(gw, event, region);

    pw->panner.tmp.showing = False;
    XFillRectangle(dpy, w, pw->panner.slider_gc, 0, 0, pw->core.width, border);
    XFillRectangle(dpy, w, pw->panner.slider_gc, 0, border, border, pw->core.height - border);
    XFillRectangle(dpy, w, pw->panner.slider_gc, pw->core.width - border, border, pw->core.width, pw->core.height - border);
    XFillRectangle(dpy, w, pw->panner.slider_gc, 0, pw->core.height - border, pw->core.width, pw->core.height);
    
    if (shadow_thickness)
        XawDrawFrame(gw, border,  border,
                     (Dimension)(pw->core.width - 2*border),
                     (Dimension)(pw->core.height - 2*border),
                     XawSUNKEN, shadow_thickness,
                     pw->panner.top_shadow_gc, pw->panner.bottom_shadow_gc);

    XClearArea(XtDisplay(pw), XtWindow(pw),
	       (int)pw->panner.last_x  + pad,
	       (int)pw->panner.last_y  + pad,
	       pw->panner.knob_width,
	       pw->panner.knob_height,
	       False);
       
    pw->panner.last_x = pw->panner.knob_x;
    pw->panner.last_y = pw->panner.knob_y;

    XFillRectangle(dpy, w, pw->panner.slider_gc, kx + shadow_thickness, ky + shadow_thickness,
                   pw->panner.knob_width - shadow_thickness, pw->panner.knob_height - shadow_thickness);

    if (shadow_thickness)
        XawDrawFrame(gw, kx, ky, pw->panner.knob_width, pw->panner.knob_height,
                     XawRAISED, shadow_thickness,
                     pw->panner.top_shadow_gc, pw->panner.bottom_shadow_gc);
}

/*ARGSUSED*/
static Boolean
XawPannerSetValues(Widget gcur, Widget greq, Widget gnew,
		   ArgList args, Cardinal *num_args)
{
    PannermWidget cur = (PannermWidget)gcur;
    PannermWidget cnew = (PannermWidget)gnew;
    Bool redisplay = False;

    if (cur->panner.foreground != cnew->panner.foreground) {
	reset_slider_gc(cnew);
	redisplay = True;
    }

    if ((cur->panner.shadow_color != cnew->panner.shadow_color
	 || cur->core.background_pixel != cnew->core.background_pixel)
	&& XtIsRealized(gnew)) 
    {
        XSetWindowBackground(XtDisplay(cnew), XtWindow(cnew), cnew->core.background_pixel);
	redisplay = True;
    }

    if (cnew->panner.resize_to_pref &&
	(cur->panner.canvas_width != cnew->panner.canvas_width
	 || cur->panner.canvas_height != cnew->panner.canvas_height
	 || cur->panner.resize_to_pref != cnew->panner.resize_to_pref)) {
	get_default_size(cnew, &cnew->core.width, &cnew->core.height);
	redisplay = True;
    }
    else if (cur->panner.canvas_width != cnew->panner.canvas_width
	     || cur->panner.canvas_height != cnew->panner.canvas_height
	     || cur->panner.internal_border != cnew->panner.internal_border) {
	rescale(cnew);			/* does a scale_knob as well */
	redisplay = True;
    }
    else {
	Bool loc = cur->panner.slider_x != cnew->panner.slider_x ||
		   cur->panner.slider_y != cnew->panner.slider_y;
	Bool siz = cur->panner.slider_width != cnew->panner.slider_width ||
	 	   cur->panner.slider_height != cnew->panner.slider_height;
	if (loc || siz || (cur->panner.allow_off != cnew->panner.allow_off
			   && cnew->panner.allow_off)) {
	    scale_knob(cnew, loc, siz);
	    redisplay = True;
	}
    }

    return (redisplay);
}

static void
XawPannerSetValuesAlmost(Widget gold, Widget gnew, XtWidgetGeometry *req,
			 XtWidgetGeometry *reply)
{
    if (reply->request_mode == 0)	/* got turned down, so cope */
	XawPannerResize(gnew);

    (*pannermWidgetClass->core_class.superclass->core_class.set_values_almost)
	(gold, gnew, req, reply);
}

static XtGeometryResult
XawPannerQueryGeometry(Widget gw, XtWidgetGeometry *intended,
		       XtWidgetGeometry *pref)
{
    PannermWidget pw = (PannermWidget)gw;

    pref->request_mode = (CWWidth | CWHeight);
    get_default_size(pw, &pref->width, &pref->height);

    if (((intended->request_mode & (CWWidth | CWHeight)) == (CWWidth | CWHeight))
	&& intended->width == pref->width && intended->height == pref->height)
	return (XtGeometryYes);
    else if (pref->width == XtWidth(pw) && pref->height == XtHeight(pw))
	return (XtGeometryNo);

    return (XtGeometryAlmost);
}


/*ARGSUSED*/
static void
ActionStart(Widget gw, XEvent *event, String *params, Cardinal *num_params)
{
    PannermWidget pw = (PannermWidget)gw;
    int x, y;

    if (!get_event_xy(pw, event, &x, &y)) {
	XBell(XtDisplay(gw), 0);
	return;
    }

    pw->panner.tmp.doing = True;
    pw->panner.tmp.startx = pw->panner.knob_x;
    pw->panner.tmp.starty = pw->panner.knob_y;
    pw->panner.tmp.dx = x - pw->panner.knob_x;
    pw->panner.tmp.dy = y - pw->panner.knob_y;
    pw->panner.tmp.x = pw->panner.knob_x;
    pw->panner.tmp.y = pw->panner.knob_y;
}

/*ARGSUSED*/
static void
ActionStop(Widget gw, XEvent *event, String *params, Cardinal *num_params)
{
    PannermWidget pw = (PannermWidget)gw;
    int x, y;

    if (get_event_xy(pw, event, &x, &y)) {
	pw->panner.tmp.x = x - pw->panner.tmp.dx;
	pw->panner.tmp.y = y - pw->panner.tmp.dy;
	if (!pw->panner.allow_off)
	    check_knob(pw, False);
    }
    pw->panner.tmp.doing = False;
}

static void
ActionAbort(Widget gw, XEvent *event, String *params, Cardinal *num_params)
{
    PannermWidget pw = (PannermWidget)gw;

    if (!pw->panner.tmp.doing)
	return;

    /* restore old position */
    pw->panner.tmp.x = pw->panner.tmp.startx;
    pw->panner.tmp.y = pw->panner.tmp.starty;
    ActionNotify(gw, event, params, num_params);

    pw->panner.tmp.doing = False;
}

static void
ActionMove(Widget gw, XEvent *event, String *params, Cardinal *num_params)
{
    PannermWidget pw = (PannermWidget)gw;
    int x, y;

    if (!pw->panner.tmp.doing)
      return;

    if (!get_event_xy(pw, event, &x, &y)) {
	XBell(XtDisplay(gw), 0);	/* should do error message */
	return;
    }

    pw->panner.tmp.x = x - pw->panner.tmp.dx;
    pw->panner.tmp.y = y - pw->panner.tmp.dy;

    ActionNotify(gw, event, params, num_params);
}


static void
ActionPage(Widget gw, XEvent *event, String *params, Cardinal *num_params)
{
    PannermWidget pw = (PannermWidget)gw;
    Cardinal zero = 0;
    Bool isin = pw->panner.tmp.doing;
    int x, y;
    Bool relx, rely;
    int pad = pw->panner.internal_border << 1;

    if (*num_params != 2) {
      XBell(XtDisplay(gw), 0);
	return;
    }

    x = parse_page_string(params[0], pw->panner.knob_width,
			  (int)XtWidth(pw) - pad, &relx);
    y = parse_page_string(params[1], pw->panner.knob_height,
			  (int)XtHeight(pw) - pad, &rely);

    if (relx)
	x += pw->panner.knob_x;
    if (rely)
	y += pw->panner.knob_y;

    if (isin) {				/* if in, then use move */
	XEvent ev;

	ev.xbutton.type = ButtonPress;
	ev.xbutton.x = x;
	ev.xbutton.y = y;
	ActionMove(gw, &ev, NULL, &zero);
    }
    else {
	pw->panner.tmp.doing = True;
	pw->panner.tmp.x = x;
	pw->panner.tmp.y = y;
	ActionNotify(gw, event, NULL, &zero);
	pw->panner.tmp.doing = False;
    }
}

/*ARGSUSED*/
static void
ActionNotify(Widget gw, XEvent *event, String *params, Cardinal *num_params)
{
    PannermWidget pw = (PannermWidget)gw;

    if (!pw->panner.tmp.doing)
	return;

    if (!pw->panner.allow_off)
	check_knob(pw, False);
    pw->panner.knob_x = pw->panner.tmp.x;
    pw->panner.knob_y = pw->panner.tmp.y;

    pw->panner.slider_x = (Position)((double)pw->panner.knob_x
				   / pw->panner.haspect + 0.5);
    pw->panner.slider_y = (Position)((double) pw->panner.knob_y
				   / pw->panner.vaspect + 0.5);
    if (!pw->panner.allow_off) {
	Position tmp;

	if (pw->panner.slider_x
	    > (tmp = (Position)pw->panner.canvas_width -
		     (Position)pw->panner.slider_width))
	    pw->panner.slider_x = tmp;
	if (pw->panner.slider_x < 0)
	    pw->panner.slider_x = 0;
	if (pw->panner.slider_y
	    > (tmp = (Position)pw->panner.canvas_height -
		     (Position)pw->panner.slider_height))
	    pw->panner.slider_y = tmp;
	if (pw->panner.slider_y < 0)
	    pw->panner.slider_y = 0;
    }

    if (pw->panner.last_x != pw->panner.knob_x ||
	pw->panner.last_y != pw->panner.knob_y) {
	XawPannerReport rep;

	XawPannerRedisplay(gw, NULL, NULL);
	rep.changed = XawPRSliderX | XawPRSliderY;
	rep.slider_x = pw->panner.slider_x;
	rep.slider_y = pw->panner.slider_y;
	rep.slider_width = pw->panner.slider_width;
	rep.slider_height = pw->panner.slider_height;
	rep.canvas_width = pw->panner.canvas_width;
	rep.canvas_height = pw->panner.canvas_height;
	XtCallCallbackList(gw, pw->panner.report_callbacks, (XtPointer)&rep);
    }
}

void CallActionPage(Widget gw, XEvent *event, String *params, Cardinal *num_params)
{
    ActionPage(gw, event, params, num_params);
}

#endif

