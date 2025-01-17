#ifndef __globals_H
#define __globals_H
/*
 * Copyright (c) 2000-2010 Stephen Williams (steve@icarus.com)
 *
 *    This source code is free software; you can redistribute it
 *    and/or modify it in source code form under the terms of the GNU
 *    General Public License as published by the Free Software
 *    Foundation; either version 2 of the License, or (at your option)
 *    any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */

#include <stddef.h>

/* This is the integer-width argument that will be passed to ivl. */
extern unsigned integer_width;

/* Perform variable substitutions on the string. */
extern char *substitutions(const char *str);

/* Add the name to the list of source files. */
extern void process_file_name(const char *name, int lib_flag);

/* Add the name to the list of library directories. */
extern void process_library_switch(const char *name);
extern void process_library_nocase_switch(const char *name);
extern void process_library2_switch(const char *name);

/* Add a new include file search directory */
extern void process_include_dir(const char *name);

/* Add a new -D define. */
extern void process_define(const char *name);

/* Set the default timescale for the simulator. */
extern void process_timescale(const char *ts_string);

#endif
