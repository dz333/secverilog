/*
 * Copyright (c) 2008-2009 Stephen Williams (steve@icarus.com)
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

#include "config.h"
#include "priv.h"
#include <assert.h>
#include <inttypes.h>
#include <stdlib.h>

void show_switch(ivl_switch_t net) {
  const char *name = ivl_switch_basename(net);
  int has_enable   = 0;
  ivl_nexus_t nexa, nexb;
  ivl_variable_type_t nex_type_a, nex_type_b;

  switch (ivl_switch_type(net)) {
  case IVL_SW_TRAN:
    fprintf(out, "  tran %s", name);
    break;
  case IVL_SW_RTRAN:
    fprintf(out, "  rtran %s", name);
    break;
  case IVL_SW_TRANIF0:
    fprintf(out, "  tranif0 %s", name);
    has_enable = 1;
    break;
  case IVL_SW_RTRANIF0:
    fprintf(out, "  rtranif0 %s", name);
    has_enable = 1;
    break;
  case IVL_SW_TRANIF1:
    fprintf(out, "  tranif1 %s", name);
    has_enable = 1;
    break;
  case IVL_SW_RTRANIF1:
    fprintf(out, "  rtranif1 %s", name);
    has_enable = 1;
    break;
  case IVL_SW_TRAN_VP:
    fprintf(out, "  tran(VP wid=%u, part=%u, off=%u) %s", ivl_switch_width(net),
            ivl_switch_part(net), ivl_switch_offset(net), name);
    break;
  }

  fprintf(out, " island=%p\n", (void *)ivl_switch_island(net));

  nexa       = ivl_switch_a(net);
  nex_type_a = nexa ? type_of_nexus(nexa) : IVL_VT_NO_TYPE;
  fprintf(out, "    A: %p <type=%s>\n", (void *)nexa,
          data_type_string(nex_type_a));

  nexb       = ivl_switch_b(net);
  nex_type_b = nexb ? type_of_nexus(nexb) : IVL_VT_NO_TYPE;
  fprintf(out, "    B: %p <type=%s>\n", (void *)nexb,
          data_type_string(nex_type_b));

  /* The A/B pins of the switch must be present, and must match. */
  if (nex_type_a == IVL_VT_NO_TYPE) {
    fprintf(out, "    A: ERROR: Type missing for pin A\n");
    stub_errors += 1;
  }
  if (nex_type_b == IVL_VT_NO_TYPE) {
    fprintf(out, "    B: ERROR: Type missing for pin B\n");
    stub_errors += 1;
  }
  if (nex_type_a != nex_type_b) {
    fprintf(out, "    A/B: ERROR: Type mismatch between pins A and B\n");
    stub_errors += 1;
  }

  if (ivl_switch_type(net) == IVL_SW_TRAN_VP) {
    /* The TRAN_VP nodes are special in that the specific
       width matters for each port and should be exactly
       right for both. */
    if (width_of_nexus(nexa) != ivl_switch_width(net)) {
      fprintf(out,
              "    A: ERROR: part vector nexus "
              "width=%u, expecting width=%u\n",
              width_of_nexus(nexa), ivl_switch_width(net));
      stub_errors += 1;
    }
    if (width_of_nexus(nexb) != ivl_switch_part(net)) {
      fprintf(out,
              "    B: ERROR: part select nexus "
              "width=%u, expecting width=%u\n",
              width_of_nexus(nexb), ivl_switch_part(net));
      stub_errors += 1;
    }
  } else {
    /* All other TRAN nodes will have matching vector
       widths, but the actual value doesn't matter. */
    if (width_of_nexus(nexa) != width_of_nexus(nexb)) {
      fprintf(out,
              "    A/B: ERROR: Width of ports don't match"
              ": A=%u, B=%u\n",
              width_of_nexus(nexa), width_of_nexus(nexb));
      stub_errors += 1;
    }
  }

  if (has_enable) {
    ivl_nexus_t nexe = ivl_switch_enable(net);
    fprintf(out, "    E: %p\n", (void *)nexe);
    if (width_of_nexus(nexe) != 1) {
      fprintf(out, "    E: ERROR: Nexus width is %u\n", width_of_nexus(nexe));
    }
  }
}
