/*
 * Copyright (c) 2007-2010 Stephen Williams (steve@icarus.com)
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

#ifndef __ivl_assert_h
#define __ivl_assert_h

#include <cassert>

#define ivl_assert(tok, expression)                                            \
  do {                                                                         \
    if (!(expression))                                                         \
      __ivl_assert(#expression, tok, __FILE__, __LINE__);                      \
  } while (0)

#define __ivl_assert(expression, tok, file, line)                              \
  do {                                                                         \
    cerr << (tok).get_fileline() << ": assert: " << file << ":" << line        \
         << ": failed assertion " << (expression) << endl;                     \
    abort();                                                                   \
  } while (0)

#endif
