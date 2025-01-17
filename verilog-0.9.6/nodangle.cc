/*
 * Copyright (c) 1999-2010 Stephen Williams (steve@icarus.com)
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

/*
 * This functor scans the design looking for dangling objects and
 * excess local signals. These deletions are not necessarily required
 * for proper functioning of anything, but they can clean up the
 * appearance of design files that are generated.
 */
#include "compiler.h"
#include "functor.h"
#include "netlist.h"

class nodangle_f : public functor_t {
public:
  void event(Design *des, NetEvent *ev);
  void signal(Design *des, NetNet *sig);

  unsigned iteration;
  unsigned stotal, etotal;
  bool scontinue, econtinue;
  bool scomplete, ecomplete;
};

void nodangle_f::event(Design *des, NetEvent *ev) {
  if (ecomplete)
    return;

  /* If there are no references to this event, then go right
     ahead and delete it. There is no use looking further at
     it. */
  if ((ev->nwait() + ev->ntrig() + ev->nexpr()) == 0) {
    delete ev;
    etotal += 1;
    return;
  }

  if (iteration == 0) {
    /* Try to remove duplicate probes from the event. This
       is done as a separate initial pass to ensure similar
       events are detected as soon as possible in subsequent
       iterations. */
    for (unsigned idx = 0; idx < ev->nprobe(); idx += 1) {
      unsigned jdx = idx + 1;
      while (jdx < ev->nprobe()) {
        NetEvProbe *ip = ev->probe(idx);
        NetEvProbe *jp = ev->probe(jdx);

        if (ip->edge() != jp->edge()) {
          jdx += 1;
          continue;
        }

        bool fully_connected = true;
        for (unsigned jpin = 0; jpin < jp->pin_count(); jpin += 1) {
          unsigned ipin       = 0;
          bool connected_flag = false;
          for (ipin = 0; ipin < ip->pin_count(); ipin += 1)
            if (connected(ip->pin(ipin), jp->pin(jpin))) {
              connected_flag = true;
              break;
            }

          if (!connected_flag) {
            fully_connected = false;
            break;
          }
        }

        if (fully_connected) {
          delete jp;
        } else {
          jdx += 1;
        }
      }
    }
    econtinue = true;
  } else {
    /* Postpone examining events in an automatic scope until the
       third (optional) pass. This will mean similar events are
       biased towards being stored in static scopes. */
    if (ev->scope()->is_auto()) {
      if (iteration == 1) {
        econtinue = true;
        return;
      }
    } else {
      if (iteration == 2) {
        return;
      }
    }

    /* Try to find all the events that are similar to me, and
       replace their references with references to me. */
    list<NetEvent *> match;
    ev->find_similar_event(match);
    for (list<NetEvent *>::iterator idx = match.begin(); idx != match.end();
         idx++) {

      NetEvent *tmp = *idx;
      assert(tmp != ev);
      tmp->replace_event(ev);
    }
  }
}

void nodangle_f::signal(Design *des, NetNet *sig) {
  if (scomplete)
    return;

  /* Cannot delete signals referenced in an expression
     or an l-value. */
  if (sig->get_refs() > 0)
    return;

  /* Cannot delete the ports of tasks, functions or modules. There
     are too many places where they are referenced. */
  if ((sig->port_type() != NetNet::NOT_A_PORT) &&
      ((sig->scope()->type() == NetScope::TASK) ||
       (sig->scope()->type() == NetScope::FUNC) ||
       (sig->scope()->type() == NetScope::MODULE)))
    return;

  /* Can't delete ports of cells. */
  if ((sig->port_type() != NetNet::NOT_A_PORT) &&
      (sig->scope()->attribute(perm_string::literal("ivl_synthesis_cell")) !=
       verinum()))
    return;

  /* Check to see if the signal is completely unconnected. If
     all the bits are unlinked, then delete it. */
  if (!sig->is_linked()) {
    delete sig;
    stotal += 1;
    return;
  }

  /* The remaining things can only be done to synthesized
     signals, not ones that appear in the original Verilog. */
  if (!sig->local_flag())
    return;

  /* Check to see if there is some significant signal connected
     to every pin of this signal. */
  unsigned significant_flags = 0;
  for (unsigned idx = 0; idx < sig->pin_count(); idx += 1) {
    Nexus *nex = sig->pin(idx).nexus();

    for (Link *cur = nex->first_nlink(); cur; cur = cur->next_nlink()) {

      if (cur == &sig->pin(idx))
        continue;

      NetNet *cursig = dynamic_cast<NetNet *>(cur->get_obj());
      if (cursig == 0)
        continue;

      if (cursig->local_flag())
        continue;

      significant_flags += 1;
      break;
    }

    if (significant_flags <= idx)
      break;
  }

  /* If every pin is connected to another significant signal,
     then I can delete this one. */
  if (significant_flags == sig->pin_count()) {
    scontinue = true;
    delete sig;
    stotal += 1;
  }
}

void nodangle(Design *des) {
  nodangle_f fun;
  fun.iteration = 0;
  fun.stotal    = 0;
  fun.etotal    = 0;
  fun.scomplete = false;
  fun.ecomplete = false;
  do {
    fun.scontinue = false;
    fun.econtinue = false;
    des->functor(&fun);
    fun.iteration += 1;
    fun.scomplete = !fun.scontinue;
    fun.ecomplete = !fun.econtinue;

    if (verbose_flag) {
      cout << " ... " << fun.iteration << " iterations"
           << " deleted " << fun.stotal << " dangling signals"
           << " and " << fun.etotal << " events." << endl;
    }

  } while (fun.scontinue || fun.econtinue);
}
