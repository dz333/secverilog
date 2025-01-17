/*
 * Copyright (c) 2003-2009 Stephen Williams (steve@icarus.com)
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

#include "priv.h"
#include <acc_user.h>
#include <string.h>
#include <vpi_user.h>

int acc_configure(PLI_INT32 config_param, const char *value) {
  int rc;
  switch (config_param) {
  case accDevelopmentVersion:
    vpi_printf("Request PLI Development Version %s\n", value);
    rc = 1;

    if (pli_trace) {
      fprintf(pli_trace, "acc_configure(accDevelopmentVersion, %s)\n", value);
    }
    break;

  case accEnableArgs:

    if (pli_trace) {
      fprintf(pli_trace, "acc_configure(accEnableArgs, %s)\n", value);
    }

    rc = 1;
    if (strcmp(value, "acc_set_scope") == 0) {
      vpi_printf("XXXX acc_configure argument: Sorry: "
                 "(accEnableArgs, %s\n",
                 value);
      rc = 0;

    } else if (strcmp(value, "no_acc_set_scope") == 0) {
      vpi_printf("XXXX acc_configure argument: Sorry: "
                 "(accEnableArgs, %s\n",
                 value);
      rc = 0;

    } else {
      vpi_printf("XXXX acc_configure argument error. "
                 "(accEnableArgs, %s(invalid)\n",
                 value);
      rc = 0;
    }

    break;

  default:

    if (pli_trace) {
      fprintf(pli_trace, "acc_configure(config=%d, %s)\n", (int)config_param,
              value);
    }

    vpi_printf("XXXX acc_configure(%d, %s)\n", (int)config_param, value);
    rc = 0;
    break;
  }

  return rc;
}
