#ifndef __ivl_target_priv_H
#define __ivl_target_priv_H
/*
 * Copyright (c) 2008 Stephen Williams (steve@icarus.com)
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

#include "ivl_target.h"
#include <inttypes.h>
#include <valarray>
#include <vector>

/*
 * This header has declarations related to the ivl_target.h API that
 * are not to be exported outside of the core via the ivl_target.h
 * interface.
 *
 * (NOTE: A lot of similar definitions exist in the t-dll.h header
 * file. That is a legacy from an earlier time before the
 * ivl_target_priv.h header file was started, and those definitions
 * should gradually be moved over to this header file.)
 */

/*
 * This is the root of a design, from the ivl_target point of few. The
 * ivl_target API uses this as the root for getting at everything else
 * in the design.
 */
struct ivl_design_s {

  int time_precision;

  ivl_process_t threads_;

  ivl_scope_t *roots_;
  unsigned nroots_;

  // Keep an array of constants objects.
  std::valarray<ivl_net_const_t> consts;

  // Keep a handy array of all of the disciplines in the design.
  std::valarray<ivl_discipline_t> disciplines;

  const class Design *self;
};

/*
 * A branch is a pair of terminals. The elaborator assures that the
 * terminals have compatible disciplines.
 */
struct ivl_branch_s {
  ivl_nexus_t pins[2];
  ivl_island_t island;
};

/*
 * Information about islands. Connected branches within a net are
 * collected into islands. Branches that are purely ddiscrete do not
 * have disciplines and do not belong to islands.
 */

struct ivl_island_s {
  ivl_discipline_t discipline;
  // user accessible flags. They are initially false, always.
  std::vector<bool> flags;
};

#endif
