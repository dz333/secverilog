#ifndef __xilinx_H
#define __xilinx_H
/*
 * Copyright (c) 2003 Stephen Williams (steve at icarus.com)
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
#ifdef HAVE_CVS_IDENT
#ident "$Id: xilinx.h,v 1.9 2007/02/26 19:49:50 steve Exp $"
#endif

/*
 * This header file includes XILINX library support functions. They
 * manage the creation and reference of cells from the library. Use
 * the xilinx_cell_* functions to get an edif_cell_t from the
 * library. The function will create the cell in the library if
 * needed, or will return the existing cell if it was already called.
 */
#include "edif.h"

/* === BUF Devices === */

/* Buffer types of devices have the BUF_O and BUF_I pin
   assignments. The BUF, INV, and certain specialized devices fit in
   this category. */
extern edif_cell_t xilinx_cell_buf(edif_xlibrary_t xlib);
extern edif_cell_t xilinx_cell_bufe(edif_xlibrary_t xlib);
extern edif_cell_t xilinx_cell_bufg(edif_xlibrary_t xlib);
extern edif_cell_t xilinx_cell_buft(edif_xlibrary_t xlib);
extern edif_cell_t xilinx_cell_inv(edif_xlibrary_t xlib);
extern edif_cell_t xilinx_cell_ibuf(edif_xlibrary_t xlib);
extern edif_cell_t xilinx_cell_obuf(edif_xlibrary_t xlib);
#define BUF_O 0
#define BUF_I 1
/* Only bufe and buft buffers have this input. */
#define BUF_T 2

/* === LUT Devices === */

/* Most Xilinx devices have LUT2/3/4 devices that take, respectively,
   2, 3 or 4 inputs. All forms have a single bit output. Also, the
   real behavior of the device will need to be specified by an INIT
   parameter string. */
extern edif_cell_t xilinx_cell_lut2(edif_xlibrary_t xlib);
extern edif_cell_t xilinx_cell_lut3(edif_xlibrary_t xlib);
extern edif_cell_t xilinx_cell_lut4(edif_xlibrary_t xlib);
#define LUT_O 0
#define LUT_I0 1
#define LUT_I1 2
#define LUT_I2 3
#define LUT_I3 4

/* === Flip-Flop Devices === */

/*
 * These are flip-flops of various sort, but similar pinouts.
 */
extern edif_cell_t xilinx_cell_fdce(edif_xlibrary_t xlib);
extern edif_cell_t xilinx_cell_fdcpe(edif_xlibrary_t xlib);
extern edif_cell_t xilinx_cell_fdre(edif_xlibrary_t xlib);
#define FDCE_Q 0
#define FDCE_C 1
#define FDCE_D 2
#define FDCE_CE 3
#define FDCE_CLR 4
#define FDCE_PRE 5

/* === Virtex/Virtex2 Carry Chain Logic === */

extern edif_cell_t xilinx_cell_mult_and(edif_xlibrary_t xlib);
#define MULT_AND_LO 0
#define MULT_AND_I0 1
#define MULT_AND_I1 2

extern edif_cell_t xilinx_cell_muxcy(edif_xlibrary_t xlib);
extern edif_cell_t xilinx_cell_muxcy_l(edif_xlibrary_t xlib);
#define MUXCY_O 0
#define MUXCY_DI 1
#define MUXCY_CI 2
#define MUXCY_S 3

extern edif_cell_t xilinx_cell_xorcy(edif_xlibrary_t xlib);
#define XORCY_O 0
#define XORCY_CI 1
#define XORCY_LI 2

/* === Virtex/Virtex2 MUX devices */
extern edif_cell_t xilinx_cell_muxf5(edif_xlibrary_t xlib);
extern edif_cell_t xilinx_cell_muxf6(edif_xlibrary_t xlib);
extern edif_cell_t xilinx_cell_muxf7(edif_xlibrary_t xlib);
extern edif_cell_t xilinx_cell_muxf8(edif_xlibrary_t xlib);
#define MUXF_O 0
#define MUXF_I0 1
#define MUXF_I1 2
#define MUXF_S 3

/* === Inheritable Methods === */

extern void virtex_logic(ivl_net_logic_t net);
extern void virtex_generic_dff(ivl_lpm_t net);
extern void virtex_eq(ivl_lpm_t net);
extern void virtex_ge(ivl_lpm_t net);
extern void virtex_mux(ivl_lpm_t net);
extern void virtex_add(ivl_lpm_t net);

extern void xilinx_common_header(ivl_design_t des);
extern void xilinx_show_footer(ivl_design_t des);
extern void xilinx_show_scope(ivl_scope_t scope);
extern void xilinx_pad(ivl_signal_t, const char *str);
extern void xilinx_logic(ivl_net_logic_t net);
extern void xilinx_mux(ivl_lpm_t net);
extern void xilinx_add(ivl_lpm_t net);
extern void xilinx_shiftl(ivl_lpm_t net);

/*
 * $Log: xilinx.h,v $
 * Revision 1.9  2007/02/26 19:49:50  steve
 *  Spelling fixes (larry doolittle)
 *
 * Revision 1.8  2003/08/15 02:23:53  steve
 *  Add synthesis support for synchronous reset.
 *
 * Revision 1.7  2003/07/04 00:10:09  steve
 *  Generate MUXF5 based 4-input N-wide muxes.
 *
 * Revision 1.6  2003/07/02 03:02:15  steve
 *  More xilinx common code.
 *
 * Revision 1.5  2003/07/02 00:25:40  steve
 *  Add xilinx support for bufif1.
 *
 * Revision 1.4  2003/06/28 04:18:47  steve
 *  Add support for wide OR/NOR gates.
 *
 * Revision 1.3  2003/06/26 03:57:05  steve
 *  Add Xilinx support for A/B MUX devices.
 *
 * Revision 1.2  2003/06/25 02:55:57  steve
 *  Virtex and Virtex2 share much code.
 *
 * Revision 1.1  2003/04/05 05:53:34  steve
 *  Move library cell management to common file.
 *
 */
#endif
