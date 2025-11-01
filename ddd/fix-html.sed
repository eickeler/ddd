# $Id$
# Fix DDD HTML code

# Set up a style
\!</head!i\
<link rel=StyleSheet HREF="style.css" type="text/css" media=screen>\

# Set up a suitable background
s!<body>!<body bgcolor="#ffffff">!

# Set up a header
\!^Node:!i\
<small class=header>
s!^Up:<a rel=up href="#(dir)">(dir)</a>!Up:<a rel=up href="http://www.gnu.org/software/ddd/">DDD home page</a>!
\!^Up:!a\
</small>\

# Add a logo before first header of manual
\!Debugging with DDD</title>!i\
<img alt="DDD - The Data Display Debugger" width=410 height=140 src="PICS/dddlogo.png">

# Add a logo before first header of themes
\!Writing DDD Themes</title>!i\
<img alt="DDD - The Data Display Debugger" width=410 height=140 src="PICS/dddlogo.png">
