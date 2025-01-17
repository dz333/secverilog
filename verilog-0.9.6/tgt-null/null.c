/*
 * Copyright (c) 2000-2008 Stephen Williams (steve@icarus.com)
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
#include "version_base.h"
#include "version_tag.h"
#include <string.h>

/*
 * This is a null target module. It does nothing.
 */

#include "ivl_target.h"

static const char *version_string =
    "Icarus Verilog NULL Code Generator " VERSION " (" VERSION_TAG ")\n\n"
    "Copyright (c) 2000-2008 Stephen Williams (steve@icarus.com)\n\n"
    "  This program is free software; you can redistribute it and/or modify\n"
    "  it under the terms of the GNU General Public License as published by\n"
    "  the Free Software Foundation; either version 2 of the License, or\n"
    "  (at your option) any later version.\n"
    "\n"
    "  This program is distributed in the hope that it will be useful,\n"
    "  but WITHOUT ANY WARRANTY; without even the implied warranty of\n"
    "  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n"
    "  GNU General Public License for more details.\n"
    "\n"
    "  You should have received a copy of the GNU General Public License "
    "along\n"
    "  with this program; if not, write to the Free Software Foundation, "
    "Inc.,\n"
    "  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.\n";

int target_design(ivl_design_t des) { return 0; }

const char *target_query(const char *key) {
  if (strcmp(key, "version") == 0)
    return version_string;

  return 0;
}
