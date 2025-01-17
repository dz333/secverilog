/*
 * Copyright (c) 1998-2012 Stephen Williams (steve@icarus.com)
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
 * This file provides the pform_dump function, that dumps the module
 * passed as a parameter. The dump is as much as possible in Verilog
 * syntax, so that a human can tell that it really does describe the
 * module in question.
 */
#include "PEvent.h"
#include "PGenerate.h"
#include "PSpec.h"
#include "discipline.h"
#include "pform.h"
#include "sexp_printer.h"
#include <iomanip>
#include <iostream>
#include <sstream>
#include <typeinfo>

ostream &operator<<(ostream &out, const PExpr &obj) {
  obj.dump(out);
  return out;
}

ostream &operator<<(ostream &out, const PEventStatement &obj) {
  obj.dump_inline(out);
  return out;
}

ostream &operator<<(ostream &o, const PDelays &d) {
  d.dump_delays(o);
  return o;
}

ostream &operator<<(ostream &o, PGate::strength_t str) {
  switch (str) {
  case PGate::HIGHZ:
    o << "highz";
    break;
  case PGate::WEAK:
    o << "weak";
    break;
  case PGate::PULL:
    o << "pull";
    break;
  case PGate::STRONG:
    o << "strong";
    break;
  case PGate::SUPPLY:
    o << "supply";
    break;
  default:
    assert(0);
  }
  return o;
}

ostream &operator<<(ostream &out, perm_string that) {
  out << that.str();
  return out;
}

ostream &operator<<(ostream &out, const index_component_t &that) {
  out << "[";
  switch (that.sel) {
  case index_component_t::SEL_BIT:
    out << *that.msb;
    break;
  case index_component_t::SEL_PART:
    out << *that.msb << ":" << *that.lsb;
    break;
  case index_component_t::SEL_IDX_UP:
    out << *that.msb << "+:" << *that.lsb;
    break;
  case index_component_t::SEL_IDX_DO:
    out << *that.msb << "-:" << *that.lsb;
    break;
  default:
    out << "???";
    break;
  }
  out << "]";
  return out;
}

ostream &operator<<(ostream &out, const name_component_t &that) {
  out << that.name.str();

  typedef std::list<index_component_t>::const_iterator index_it_t;
  for (index_it_t idx = that.index.begin(); idx != that.index.end(); idx++) {

    out << *idx;
  }
  return out;
}

ostream &operator<<(ostream &o, const pform_name_t &that) {
  pform_name_t::const_iterator cur;

  cur = that.begin();
  o << *cur;

  cur++;
  while (cur != that.end()) {
    o << "." << *cur;
    cur++;
  }

  return o;
}

std::ostream &operator<<(std::ostream &out, ivl_process_type_t pt) {
  switch (pt) {
  case IVL_PR_INITIAL:
    out << "initial";
    break;
  case IVL_PR_ALWAYS:
    out << "always";
    break;
  }
  return out;
}

std::ostream &operator<<(std::ostream &out, ivl_dis_domain_t dom) {
  switch (dom) {
  case IVL_DIS_NONE:
    out << "no-domain";
    break;
  case IVL_DIS_DISCRETE:
    out << "discrete";
    break;
  case IVL_DIS_CONTINUOUS:
    out << "continuous";
    break;
  default:
    assert(0);
    break;
  }
  return out;
}

static void dump_attributes_map(ostream &out,
                                const map<perm_string, PExpr *> &attributes,
                                int ind) {
  for (map<perm_string, PExpr *>::const_iterator idx = attributes.begin();
       idx != attributes.end(); idx++) {

    out << setw(ind) << ""
        << "(* " << (*idx).first;
    if ((*idx).second) {
      out << " = " << *(*idx).second;
    }
    out << " *)" << endl;
  }
}

void PExpr::dump(ostream &out) const { out << typeid(*this).name(); }

void PExpr::dumpz3(SexpPrinter &out) const { out << typeid(*this).name(); }

void PEConcat::dump(ostream &out) const {
  if (repeat_)
    out << "{" << *repeat_;

  if (parms_.count() == 0) {
    out << "{}";
    return;
  }

  out << "{";
  if (parms_[0])
    out << *parms_[0];
  for (unsigned idx = 1; idx < parms_.count(); idx += 1) {
    out << ", ";
    if (parms_[idx])
      out << *parms_[idx];
  }

  out << "}";

  if (repeat_)
    out << "}";
}

void PEConcat::dumpz3(SexpPrinter &) const {
  throw "Cannot dump concat to z3 constraints";
}

void PECallFunction::dump(ostream &out) const {
  out << path_ << "(";

  if (parms_.size() > 0) {
    if (parms_[0])
      parms_[0]->dump(out);
    for (unsigned idx = 1; idx < parms_.size(); ++idx) {
      out << ", ";
      if (parms_[idx])
        parms_[idx]->dump(out);
    }
  }
  out << ")";
}

void PECallFunction::dumpz3(SexpPrinter &out) const {
  throw "Cannot dump function call to z3 constraints";
}

void PEEvent::dump(ostream &out) const {
  switch (type_) {
  case PEEvent::ANYEDGE:
    break;
  case PEEvent::POSEDGE:
    out << "posedge ";
    break;
  case PEEvent::NEGEDGE:
    out << "negedge ";
    break;
  case PEEvent::POSITIVE:
    out << "positive ";
    break;
  }
  out << *expr_;
}

void PEEvent::dumpz3(SexpPrinter &) const {
  throw "Cannot dump event to z3 constraints";
}

void PEFNumber::dump(ostream &out) const { out << value(); }

void PEFNumber::dumpz3(SexpPrinter &printer) const {
  // we shouldn't have floats in our constraints
  printer << std::to_string(value().as_long());
}

void PENumber::dump(ostream &out) const { out << value(); }

void PENumber::dumpz3(SexpPrinter &printer) const {
  printer << std::to_string(value().as_long());
}

void PEBoolean::dump(ostream &out) const {
  out << (value() ? "true" : "false");
}

void PEBoolean::dumpz3(SexpPrinter &printer) const {
  printer << std::string(value() ? "true" : "false");
}

void PEIdent::dump(ostream &out) const { out << path(); }

void PEIdent::dumpz3(SexpPrinter &printer) const {
  std::list<index_component_t>::const_iterator idxit =
      path_.back().index.begin();
  if (idxit != path_.back().index.end()) {
    //(select name idx)
    PExpr *msb = idxit->msb;
    PExpr *lsb = idxit->lsb;
    if (!msb || lsb) { // just dump normally if its form x[msb:lsb]
      std::stringstream str;
      dump(str);
      printer << str.str();
    } else {
      perm_string base_name = peek_tail_name(path_);
      printer.startList("select");
      printer << base_name.str();
      msb->dumpz3(printer);
      printer.endList();
    }
  } else {
    // no index information, just dump it!
    std::stringstream tmp;
    dump(tmp);
    printer << tmp.str();
  }
  return;
}

void PEIdent::dumpEq(SexpPrinter &printer, int val) const {
  printer.startList("=");
  dumpz3(printer);
  printer << std::to_string(val);
  printer.endList();
}

void PEString::dump(ostream &out) const { out << "\"" << text_ << "\""; }

void PEString::dumpz3(SexpPrinter &printer) const {
  std::stringstream tmp;
  dump(tmp);
  printer << tmp.str();
}

void PETernary::dump(ostream &out) const {
  out << "(" << *expr_ << ")?(" << *tru_ << "):(" << *fal_ << ")";
}

void PETernary::dumpz3(SexpPrinter &printer) const {
  printer.startList("ite");
  auto exident = dynamic_cast<PEIdent *>(expr_);
  if (exident)
    exident->dumpEq(printer, 1);
  else
    expr_->dumpz3(printer);
  tru_->dumpz3(printer);
  fal_->dumpz3(printer);
  printer.endList();
}

void PEUnary::dump(ostream &out) const {
  switch (op_) {
  case 'm':
    out << "abs";
    break;
  case 'N':
    out << "not";
    break;
  default:
    out << op_;
    break;
  }
  out << "(" << *expr_ << ")";
}
void PEUnary::dumpz3(SexpPrinter &printer) const {

  PEIdent *exident = dynamic_cast<PEIdent *>(expr_);
  bool doEq        = false;
  printer.startList();
  switch (op_) {
  case 'm':
    printer << "abs";
    break;
  case '!':
  case 'N':
    printer << "not";
    doEq = true;
    break;

  default:
    printer << std::string(1, op_);
    break;
  }
  if (exident && doEq) {
    exident->dumpEq(printer, 1);
  } else {
    expr_->dumpz3(printer);
  }
  printer.endList();
}

void PEBinary::dump(ostream &out) const {
  /* Handle some special cases, where the operators are written
     in function notation. */
  // fprintf(stderr, "op:%c\n", op_);
  if (op_ == 'm') {
    out << "min(" << *left_ << "," << *right_ << ")";
    return;
  }
  if (op_ == 'M') {
    out << "min(" << *left_ << "," << *right_ << ")";
    return;
  }
  if (op_ == 'e') {
    out << "= " << *left_ << " " << *right_;
    return;
  }
  if (op_ == 'o') {
    out << "or "
        << "(" << *left_ << ") (" << *right_ << ")";
    return;
  }
  if (op_ == 'a') {
    out << "and "
        << "(" << *left_ << ") (" << *right_ << ")";
    return;
  }
  if (op_ == 'L') {

    out << "<= " << *left_ << " " << *right_;
    return;
  }
  if (op_ == 'G') {
    // out << "<= "<< "(" << *left_ << ") (" << *right_ << ")";
    out << ">= " << *left_ << " " << *right_;
    return;
  }
  if (op_ == 'n') {
    out << "not( = " << *left_ << " " << *right_ << ")";
    return;
  }

  out << "(" << *left_ << ")";
  switch (op_) {
  case 'E':
    out << "===";
    break;
  case 'l':
    out << "<<";
    break;
  case 'N':
    out << "!==";
    break;
  case 'p':
    out << "**";
    break;
  case 'R':
    out << ">>>";
    break;
  case 'r':
    out << ">>";
    break;
  default:
    out << op_;
    break;
  }
  out << "(" << *right_ << ")";
}
void PEBinary::dumpz3(SexpPrinter &printer) const {
  PEIdent *liden = dynamic_cast<PEIdent *>(left_);
  PEIdent *riden = dynamic_cast<PEIdent *>(right_);
  if (op_ == 'm') {
    printer.startList("min");
    left_->dumpz3(printer);
    right_->dumpz3(printer);
    printer.endList();
    return;
  }
  if (op_ == 'M') {
    printer.startList("max");
    left_->dumpz3(printer);
    right_->dumpz3(printer);
    printer.endList();
    return;
  }
  if (op_ == 'e') {
    printer.startList("=");
    left_->dumpz3(printer);
    right_->dumpz3(printer);
    printer.endList();
    return;
  }
  if (op_ == 'o') {
    printer.startList("or");
    if (liden) {
      liden->dumpEq(printer, 1);
    } else {
      left_->dumpz3(printer);
    }
    if (riden) {
      riden->dumpEq(printer, 1);
    } else {
      right_->dumpz3(printer);
    }
    printer.endList();
    return;
  }
  if (op_ == 'a') {
    printer.startList("and");
    if (liden) {
      liden->dumpEq(printer, 1);
    } else {
      left_->dumpz3(printer);
    }
    if (riden) {
      riden->dumpEq(printer, 1);
    } else {
      right_->dumpz3(printer);
    }
    printer.endList();
    return;
  }
  if (op_ == 'L') {
    printer.startList("<=");
    left_->dumpz3(printer);
    right_->dumpz3(printer);
    printer.endList();
    return;
  }
  if (op_ == 'G') {
    printer.startList(">=");
    left_->dumpz3(printer);
    right_->dumpz3(printer);
    printer.endList();
    return;
  }
  if (op_ == 'n') {
    printer.startList("not");
    printer.startList("=");
    left_->dumpz3(printer);
    right_->dumpz3(printer);
    printer.endList();
    printer.endList();
    return;
  }
  if ((op_ == '>') || (op_ == '<') || (op_ == '+') || (op_ == '-')) {
    printer.startList(std::string(1, op_));
    left_->dumpz3(printer);
    right_->dumpz3(printer);
    printer.endList();
    return;
  }
  if (op_ == '%') {
    printer.startList("mod");
    left_->dumpz3(printer);
    right_->dumpz3(printer);
    printer.endList();
    return;
  }
  auto msg = new std::string("No support for given binary operator: ");
  *msg += op_;
  throw std::runtime_error(*msg);
}

void PWire::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << "" << type_;

  switch (port_type_) {
  case NetNet::PIMPLICIT:
    out << " implicit input";
    break;
  case NetNet::PINPUT:
    out << " input";
    break;
  case NetNet::POUTPUT:
    out << " output";
    break;
  case NetNet::PINOUT:
    out << " inout";
    break;
  case NetNet::NOT_A_PORT:
    break;
  }

  out << " " << data_type_;

  if (signed_) {
    out << " signed";
  }

  if (discipline_) {
    out << " discipline<" << discipline_->name() << ">";
  }

  if (port_set_) {
    if (port_msb_ == 0) {
      out << " port<scalar>";
    } else {
      out << " port[" << *port_msb_ << ":" << *port_lsb_ << "]";
    }
  }
  if (net_set_) {
    if (net_msb_ == 0) {
      out << " net<scalar>";
    } else {
      out << " net[" << *net_msb_ << ":" << *net_lsb_ << "]";
    }
  }

  out << " " << name_;

  // If the wire has indices, dump them.
  if (lidx_ || ridx_) {
    out << "[";
    if (lidx_)
      out << *lidx_;
    if (ridx_)
      out << ":" << *ridx_;
    out << "]";
  }

  out << ";" << endl;
  dump_attributes_map(out, attributes, 8);
}

void PGate::dump_pins(ostream &out) const {
  if (pin_count()) {
    if (pin(0))
      out << *pin(0);

    for (unsigned idx = 1; idx < pin_count(); idx += 1) {
      out << ", ";
      if (pin(idx))
        out << *pin(idx);
    }
  }
}

void PDelays::dump_delays(ostream &out) const {
  if (delay_[0] && delay_[1] && delay_[2])
    out << "#(" << *delay_[0] << "," << *delay_[1] << "," << *delay_[2] << ")";
  else if (delay_[0] && delay_[1])
    out << "#(" << *delay_[0] << "," << *delay_[1] << ")";
  else if (delay_[0])
    out << "#" << *delay_[0];
  else
    out << "#0";
}

void PGate::dump_delays(ostream &out) const { delay_.dump_delays(out); }

void PGate::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << "" << typeid(*this).name() << " ";
  delay_.dump_delays(out);
  out << " " << get_name() << "(";
  dump_pins(out);
  out << ");" << endl;
}

void PGAssign::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << "";
  out << "assign (" << strength0() << "0 " << strength1() << "1) ";
  dump_delays(out);
  out << " " << *pin(0) << " = " << *pin(1) << ";" << endl;
}

void PGBuiltin::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << "";
  switch (type()) {
  case PGBuiltin::BUFIF0:
    out << "bufif0 ";
    break;
  case PGBuiltin::BUFIF1:
    out << "bufif1 ";
    break;
  case PGBuiltin::NOTIF0:
    out << "bufif0 ";
    break;
  case PGBuiltin::NOTIF1:
    out << "bufif1 ";
    break;
  case PGBuiltin::NAND:
    out << "nand ";
    break;
  case PGBuiltin::NMOS:
    out << "nmos ";
    break;
  case PGBuiltin::RNMOS:
    out << "rnmos ";
    break;
  case PGBuiltin::RPMOS:
    out << "rpmos ";
    break;
  case PGBuiltin::PMOS:
    out << "pmos ";
    break;
  case PGBuiltin::RCMOS:
    out << "rcmos ";
    break;
  case PGBuiltin::CMOS:
    out << "cmos ";
    break;
  default:
    out << "builtin gate ";
  }

  out << "(" << strength0() << "0 " << strength1() << "1) ";
  dump_delays(out);
  out << " " << get_name();

  if (msb_) {
    out << " [" << *msb_ << ":" << *lsb_ << "]";
  }

  out << "(";
  dump_pins(out);
  out << ");" << endl;
}

void PGModule::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << "" << type_ << " ";

  // If parameters are overridden by order, dump them.
  if (overrides_ && overrides_->count() > 0) {
    assert(parms_ == 0);
    out << "#(";

    if ((*overrides_)[0] == 0)
      out << "<nil>";
    else
      out << *((*overrides_)[0]);
    for (unsigned idx = 1; idx < overrides_->count(); idx += 1) {
      out << "," << *((*overrides_)[idx]);
    }
    out << ") ";
  }

  // If parameters are overridden by name, dump them.
  if (parms_) {
    assert(overrides_ == 0);
    out << "#(";
    out << "." << parms_[0].name << "(" << *parms_[0].parm << ")";
    for (unsigned idx = 1; idx < nparms_; idx += 1) {
      out << ", ." << parms_[idx].name << "(" << *parms_[idx].parm << ")";
    }
    out << ") ";
  }

  out << get_name();

  // If the module is arrayed, print the index expressions.
  if (msb_ || lsb_) {
    out << "[";
    if (msb_)
      out << *msb_;
    out << ":";
    if (lsb_)
      out << *lsb_;
    out << "]";
  }

  out << "(";
  if (pins_) {
    out << "." << pins_[0].name << "(";
    if (pins_[0].parm)
      out << *pins_[0].parm;
    out << ")";
    for (unsigned idx = 1; idx < npins_; idx += 1) {
      out << ", ." << pins_[idx].name << "(";
      if (pins_[idx].parm)
        out << *pins_[idx].parm;
      out << ")";
    }
  } else {
    dump_pins(out);
  }
  out << ");" << endl;
}

void Statement::dump(ostream &out, unsigned ind) const {
  /* I give up. I don't know what type this statement is,
     so just print the C++ typeid and let the user figure
     it out. */
  out << setw(ind) << "";
  out << "/* " << get_fileline() << ": " << typeid(*this).name() << " */ ;"
      << endl;
  dump_attributes_map(out, attributes, ind + 2);
}

void AContrib::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << "";
  out << *lval_ << " <+ " << *rval_ << "; /* " << get_fileline() << " */"
      << endl;
}

void PAssign::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << "" << *lval() << " = ";
  if (delay_)
    out << "#" << *delay_ << " ";
  if (count_)
    out << "repeat(" << *count_ << ") ";
  if (event_)
    out << *event_ << " ";
  out << *rval() << ";"
      << "  /* " << get_fileline() << " */" << endl;
}

void PAssignNB::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << "" << *lval() << " <= ";
  if (delay_)
    out << "#" << *delay_ << " ";
  if (count_)
    out << "repeat(" << *count_ << ") ";
  if (event_)
    out << *event_ << " ";
  out << *rval() << ";"
      << "  /* " << get_fileline() << " */" << endl;
}

void PBlock::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "begin";
  if (pscope_name() != 0)
    out << " : " << pscope_name();
  out << endl;

  if (pscope_name() != 0) {
    dump_parameters_(out, ind + 2);

    dump_localparams_(out, ind + 2);

    dump_events_(out, ind + 2);

    dump_wires_(out, ind + 2);
  }

  for (unsigned idx = 0; idx < list_.count(); idx += 1) {
    if (list_[idx])
      list_[idx]->dump(out, ind + 2);
    else
      out << setw(ind + 2) << ""
          << "/* NOOP */ ;" << endl;
  }

  out << setw(ind) << ""
      << "end" << endl;
}

void PCallTask::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << "" << path_;

  if (parms_.count() > 0) {
    out << "(";
    if (parms_[0])
      out << *parms_[0];

    for (unsigned idx = 1; idx < parms_.count(); idx += 1) {
      out << ", ";
      if (parms_[idx])
        out << *parms_[idx];
    }
    out << ")";
  }

  out << "; /* " << get_fileline() << " */" << endl;
}

void PCase::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << "";
  switch (type_) {
  case NetCase::EQ:
    out << "case";
    break;
  case NetCase::EQX:
    out << "casex";
    break;
  case NetCase::EQZ:
    out << "casez";
    break;
  }
  out << " (" << *expr_ << ") /* " << get_fileline() << " */" << endl;
  dump_attributes_map(out, attributes, ind + 2);

  for (unsigned idx = 0; idx < items_->count(); idx += 1) {
    PCase::Item *cur = (*items_)[idx];

    if (cur->expr.count() == 0) {
      out << setw(ind + 2) << ""
          << "default:";

    } else {
      out << setw(ind + 2) << "" << *cur->expr[0];

      for (unsigned e = 1; e < cur->expr.count(); e += 1)
        out << ", " << *cur->expr[e];

      out << ":";
    }

    if (cur->stat) {
      out << endl;
      cur->stat->dump(out, ind + 6);
    } else {
      out << " ;" << endl;
    }
  }

  out << setw(ind) << ""
      << "endcase" << endl;
}

void PCondit::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "if (" << *expr_ << ")" << endl;
  if (if_)
    if_->dump(out, ind + 3);
  else
    out << setw(ind) << ";" << endl;
  if (else_) {
    out << setw(ind) << ""
        << "else" << endl;
    else_->dump(out, ind + 3);
  }
}

void PCAssign::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "assign " << *lval_ << " = " << *expr_ << "; /* " << get_fileline()
      << " */" << endl;
}

void PDeassign::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "deassign " << *lval_ << "; /* " << get_fileline() << " */" << endl;
}

void PDelayStatement::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "#" << *delay_ << " /* " << get_fileline() << " */";
  if (statement_) {
    out << endl;
    statement_->dump(out, ind + 2);
  } else {
    out << " /* noop */;" << endl;
  }
}

void PDisable::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "disable " << scope_ << "; /* " << get_fileline() << " */" << endl;
}

void PEventStatement::dump(ostream &out, unsigned ind) const {
  if (expr_.count() == 0) {
    out << setw(ind) << ""
        << "@* ";

  } else {
    out << setw(ind) << ""
        << "@(" << *(expr_[0]);
    if (expr_.count() > 1)
      for (unsigned idx = 1; idx < expr_.count(); idx += 1)
        out << " or " << *(expr_[idx]);

    out << ")";
  }

  if (statement_) {
    out << endl;
    statement_->dump(out, ind + 2);
  } else {
    out << " ;" << endl;
  }
}

void PEventStatement::dump_inline(ostream &out) const {
  assert(statement_ == 0);

  if (expr_.count() == 0) {
    out << "@* ";

  } else {
    out << "@(" << *(expr_[0]);
    if (expr_.count() > 1)
      for (unsigned idx = 1; idx < expr_.count(); idx += 1)
        out << " or " << *(expr_[idx]);

    out << ")";
  }
}

void PForce::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "force " << *lval_ << " = " << *expr_ << "; /* " << get_fileline()
      << " */" << endl;
}

void PForever::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "forever /* " << get_fileline() << " */" << endl;
  statement_->dump(out, ind + 3);
}

void PForStatement::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "for (" << *name1_ << " = " << *expr1_ << "; " << *cond_ << "; "
      << *name2_ << " = " << *expr2_ << ")" << endl;
  statement_->dump(out, ind + 3);
}

void PFunction::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "function ";
  if (is_auto_)
    cout << "automatic ";
  switch (return_type_.type) {
  case PTF_NONE:
    out << "?none? ";
    break;
  case PTF_REG:
    out << "reg ";
    break;
  case PTF_REG_S:
    out << "reg_s ";
    break;
  case PTF_INTEGER:
    out << "integer ";
    break;
  case PTF_REAL:
    out << "real ";
    break;
  case PTF_REALTIME:
    out << "realtime ";
    break;
  case PTF_TIME:
    out << "time ";
    break;
  }

  if (return_type_.range) {
    out << "[";
    out << "] ";
  }

  out << pscope_name() << ";" << endl;

  if (ports_)
    for (unsigned idx = 0; idx < ports_->count(); idx += 1) {
      out << setw(ind) << "";
      out << "input ";
      out << (*ports_)[idx]->basename() << ";" << endl;
    }

  dump_parameters_(out, ind);

  dump_localparams_(out, ind);

  dump_events_(out, ind);

  dump_wires_(out, ind);

  if (statement_)
    statement_->dump(out, ind);
  else
    out << setw(ind) << ""
        << "/* NOOP */" << endl;
}

void PRelease::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "release " << *lval_ << "; /* " << get_fileline() << " */" << endl;
}

void PRepeat::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "repeat (" << *expr_ << ")" << endl;
  statement_->dump(out, ind + 3);
}

void PTask::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "task ";
  if (is_auto_)
    cout << "automatic ";
  out << pscope_name() << ";" << endl;
  if (ports_)
    for (unsigned idx = 0; idx < ports_->count(); idx += 1) {
      out << setw(ind) << "";
      switch ((*ports_)[idx]->get_port_type()) {
      case NetNet::PINPUT:
        out << "input ";
        break;
      case NetNet::POUTPUT:
        out << "output ";
        break;
      case NetNet::PINOUT:
        out << "inout ";
        break;
      default:
        assert(0);
        break;
      }
      out << (*ports_)[idx]->basename() << ";" << endl;
    }

  dump_parameters_(out, ind);

  dump_localparams_(out, ind);

  dump_events_(out, ind);

  dump_wires_(out, ind);

  if (statement_)
    statement_->dump(out, ind);
  else
    out << setw(ind) << ""
        << "/* NOOP */" << endl;
}

void PTrigger::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "-> " << event_ << ";" << endl;
}

void PWhile::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "while (" << *cond_ << ")" << endl;
  statement_->dump(out, ind + 3);
}

void PProcess::dump(ostream &out, unsigned ind) const {
  out << setw(ind) << "" << type_ << " /* " << get_fileline() << " */" << endl;

  dump_attributes_map(out, attributes, ind + 2);

  statement_->dump(out, ind + 2);
}

void AProcess::dump(ostream &out, unsigned ind) const {
  switch (type_) {
  case IVL_PR_INITIAL:
    out << setw(ind) << ""
        << "analog initial";
    break;
  case IVL_PR_ALWAYS:
    out << setw(ind) << ""
        << "analog";
    break;
  }

  out << " /* " << get_fileline() << " */" << endl;

  dump_attributes_map(out, attributes, ind + 2);

  statement_->dump(out, ind + 2);
}

void PSpecPath::dump(std::ostream &out, unsigned ind) const {
  out << setw(ind) << ""
      << "specify path ";

  if (condition)
    out << "if (" << *condition << ") ";

  out << "(";
  if (edge) {
    if (edge > 0)
      out << "posedge ";
    else
      out << "negedge ";
  }

  for (unsigned idx = 0; idx < src.size(); idx += 1) {
    if (idx > 0)
      out << ", ";
    assert(src[idx]);
    out << src[idx];
  }

  out << " ";
  if (polarity)
    out << polarity;
  if (full_flag)
    out << "*> ";
  else
    out << "=> ";

  if (data_source_expression)
    out << "(";

  for (unsigned idx = 0; idx < dst.size(); idx += 1) {
    if (idx > 0)
      out << ", ";
    assert(dst[idx]);
    out << dst[idx];
  }

  if (data_source_expression)
    out << " : " << *data_source_expression << ")";

  out << ") = (";
  for (unsigned idx = 0; idx < delays.size(); idx += 1) {
    if (idx > 0)
      out << ", ";
    assert(delays[idx]);
    out << *delays[idx];
  }
  out << ");" << endl;
}

void PGenerate::dump(ostream &out, unsigned indent) const {
  out << setw(indent) << ""
      << "generate(" << id_number << ")";

  switch (scheme_type) {
  case GS_NONE:
    break;
  case GS_LOOP:
    out << " for (" << loop_index << "=" << *loop_init << "; " << *loop_test
        << "; " << loop_index << "=" << *loop_step << ")";
    break;
  case GS_CONDIT:
    out << " if (" << *loop_test << ")";
    break;
  case GS_ELSE:
    out << " else !(" << *loop_test << ")";
    break;
  case GS_CASE:
    out << " case (" << *loop_test << ")";
    break;
  case GS_CASE_ITEM:
    if (loop_test)
      out << " (" << *loop_test << ") == (" << *parent->loop_test << ")";
    else
      out << " default:";
    break;
  case GS_NBLOCK:
    out << " begin";
  }

  if (scope_name)
    out << " : " << scope_name;

  out << endl;

  dump_localparams_(out, indent + 2);

  typedef list<PGenerate::named_expr_t>::const_iterator parm_hiter_t;
  for (parm_hiter_t cur = defparms.begin(); cur != defparms.end(); ++cur) {
    out << setw(indent + 2) << ""
        << "defparam " << (*cur).first << " = ";
    if ((*cur).second)
      out << *(*cur).second << ";" << endl;
    else
      out << "/* ERROR */;" << endl;
  }

  dump_events_(out, indent + 2);

  dump_wires_(out, indent + 2);

  for (list<PGate *>::const_iterator idx = gates.begin(); idx != gates.end();
       idx++) {
    (*idx)->dump(out, indent + 2);
  }

  for (list<PProcess *>::const_iterator idx = behaviors.begin();
       idx != behaviors.end(); idx++) {
    (*idx)->dump(out, indent + 2);
  }

  for (list<AProcess *>::const_iterator idx = analog_behaviors.begin();
       idx != analog_behaviors.end(); idx++) {
    (*idx)->dump(out, indent + 2);
  }

  typedef map<perm_string, LineInfo *>::const_iterator genvar_iter_t;
  for (genvar_iter_t cur = genvars.begin(); cur != genvars.end(); cur++) {
    out << setw(indent + 2) << ""
        << "genvar " << ((*cur).first) << ";" << endl;
  }

  for (list<PGenerate *>::const_iterator idx = generate_schemes.begin();
       idx != generate_schemes.end(); idx++) {
    (*idx)->dump(out, indent + 2);
  }

  if (scheme_type == GS_NBLOCK) {
    out << setw(indent) << ""
        << "end endgenerate" << endl;
  } else {
    out << setw(indent) << ""
        << "endgenerate" << endl;
  }
}

void LexicalScope::dump_parameters_(ostream &out, unsigned indent) const {
  typedef map<perm_string, param_expr_t>::const_iterator parm_iter_t;
  for (parm_iter_t cur = parameters.begin(); cur != parameters.end(); cur++) {
    out << setw(indent) << ""
        << "parameter " << (*cur).second.type << " ";
    if ((*cur).second.signed_flag)
      out << "signed ";
    if ((*cur).second.msb)
      out << "[" << *(*cur).second.msb << ":" << *(*cur).second.lsb << "] ";
    out << (*cur).first << " = ";
    if ((*cur).second.expr)
      out << *(*cur).second.expr;
    else
      out << "/* ERROR */";
    for (LexicalScope::range_t *tmp = (*cur).second.range; tmp;
         tmp                        = tmp->next) {
      if (tmp->exclude_flag)
        out << " exclude ";
      else
        out << " from ";
      if (tmp->low_open_flag)
        out << "(";
      else
        out << "[";
      if (tmp->low_expr)
        out << *(tmp->low_expr);
      else if (tmp->low_open_flag == false)
        out << "-inf";
      else
        out << "<nil>";
      out << ":";
      if (tmp->high_expr)
        out << *(tmp->high_expr);
      else if (tmp->high_open_flag == false)
        out << "inf";
      else
        out << "<nil>";
      if (tmp->high_open_flag)
        out << ")";
      else
        out << "]";
    }
    out << ";" << endl;
  }
}

void LexicalScope::dump_localparams_(ostream &out, unsigned indent) const {
  typedef map<perm_string, param_expr_t>::const_iterator parm_iter_t;
  for (parm_iter_t cur = localparams.begin(); cur != localparams.end(); cur++) {
    out << setw(indent) << ""
        << "localparam ";
    if ((*cur).second.msb)
      out << "[" << *(*cur).second.msb << ":" << *(*cur).second.lsb << "] ";
    out << (*cur).first << " = ";
    if ((*cur).second.expr)
      out << *(*cur).second.expr << ";" << endl;
    else
      out << "/* ERROR */;" << endl;
  }
}

void LexicalScope::dump_events_(ostream &out, unsigned indent) const {
  for (map<perm_string, PEvent *>::const_iterator cur = events.begin();
       cur != events.end(); cur++) {
    PEvent *ev = (*cur).second;
    out << setw(indent) << ""
        << "event " << ev->name() << "; // " << ev->get_fileline() << endl;
  }
}

void LexicalScope::dump_wires_(ostream &out, unsigned indent) const {
  // Iterate through and display all the wires.
  for (map<perm_string, PWire *>::const_iterator wire = wires.begin();
       wire != wires.end(); wire++) {

    (*wire).second->dump(out, indent);
  }
}

void Module::dump(ostream &out) const {
  if (attributes.begin() != attributes.end()) {
    out << "(* ";
    for (map<perm_string, PExpr *>::const_iterator idx = attributes.begin();
         idx != attributes.end(); idx++) {
      if (idx != attributes.begin()) {
        out << " , ";
      }
      out << (*idx).first;
      if ((*idx).second) {
        out << " = " << *(*idx).second;
      }
    }
    out << " *)  ";
  }

  out << "module " << mod_name() << ";";
  if (is_cell)
    out << "  // Is in `celldefine.";
  out << endl;

  for (unsigned idx = 0; idx < ports.size(); idx += 1) {
    port_t *cur = ports[idx];

    if (cur == 0) {
      out << "    unconnected" << endl;
      continue;
    }

    out << "    ." << cur->name << "(" << *cur->expr[0];
    for (unsigned wdx = 1; wdx < cur->expr.size(); wdx += 1) {
      out << ", " << *cur->expr[wdx];
    }

    out << ")" << endl;
  }

  dump_parameters_(out, 4);

  dump_localparams_(out, 4);

  typedef map<perm_string, LineInfo *>::const_iterator genvar_iter_t;
  for (genvar_iter_t cur = genvars.begin(); cur != genvars.end(); cur++) {
    out << "    genvar " << ((*cur).first) << ";" << endl;
  }

  typedef list<PGenerate *>::const_iterator genscheme_iter_t;
  for (genscheme_iter_t cur = generate_schemes.begin();
       cur != generate_schemes.end(); cur++) {
    (*cur)->dump(out, 4);
  }

  typedef map<perm_string, PExpr *>::const_iterator specparm_iter_t;
  for (specparm_iter_t cur = specparams.begin(); cur != specparams.end();
       cur++) {
    out << "    specparam " << (*cur).first << " = " << *(*cur).second << ";"
        << endl;
  }

  typedef list<Module::named_expr_t>::const_iterator parm_hiter_t;
  for (parm_hiter_t cur = defparms.begin(); cur != defparms.end(); cur++) {
    out << "    defparam " << (*cur).first << " = ";
    if ((*cur).second)
      out << *(*cur).second << ";" << endl;
    else
      out << "/* ERROR */;" << endl;
  }

  dump_events_(out, 4);

  // Iterate through and display all the wires.
  dump_wires_(out, 4);

  // Dump the task definitions.
  typedef map<perm_string, PTask *>::const_iterator task_iter_t;
  for (task_iter_t cur = tasks.begin(); cur != tasks.end(); cur++) {
    out << "    task " << (*cur).first << ";" << endl;
    (*cur).second->dump(out, 6);
    out << "    endtask;" << endl;
  }

  // Dump the function definitions.
  typedef map<perm_string, PFunction *>::const_iterator func_iter_t;
  for (func_iter_t cur = funcs.begin(); cur != funcs.end(); cur++) {
    out << "    function " << (*cur).first << ";" << endl;
    (*cur).second->dump(out, 6);
    out << "    endfunction;" << endl;
  }

  // Iterate through and display all the gates
  for (list<PGate *>::const_iterator gate = gates_.begin();
       gate != gates_.end(); gate++) {

    (*gate)->dump(out);
  }

  for (list<PProcess *>::const_iterator behav = behaviors.begin();
       behav != behaviors.end(); behav++) {

    (*behav)->dump(out, 4);
  }

  for (list<AProcess *>::const_iterator idx = analog_behaviors.begin();
       idx != analog_behaviors.end(); idx++) {
    (*idx)->dump(out, 4);
  }

  for (list<PSpecPath *>::const_iterator spec = specify_paths.begin();
       spec != specify_paths.end(); spec++) {

    (*spec)->dump(out, 4);
  }

  out << "endmodule" << endl;
}

void pform_dump(ostream &out, Module *mod) { mod->dump(out); }

void PUdp::dump(ostream &out) const {
  out << "primitive " << name_ << "(" << ports[0];
  for (unsigned idx = 1; idx < ports.count(); idx += 1)
    out << ", " << ports[idx];
  out << ");" << endl;

  if (sequential)
    out << "    reg " << ports[0] << ";" << endl;

  out << "    table" << endl;
  for (unsigned idx = 0; idx < tinput.count(); idx += 1) {
    out << "     ";
    for (unsigned chr = 0; chr < tinput[idx].length(); chr += 1)
      out << " " << tinput[idx][chr];

    if (sequential)
      out << " : " << tcurrent[idx];

    out << " : " << toutput[idx] << " ;" << endl;
  }
  out << "    endtable" << endl;

  if (sequential)
    out << "    initial " << ports[0] << " = 1'b" << initial << ";" << endl;

  // Dump the attributes for the primitive as attribute
  // statements.
  for (map<string, PExpr *>::const_iterator idx = attributes.begin();
       idx != attributes.end(); idx++) {
    out << "    attribute " << (*idx).first;
    if ((*idx).second)
      out << " = " << *(*idx).second;
    out << endl;
  }

  out << "endprimitive" << endl;
}

void pform_dump(std::ostream &out, const ivl_nature_s *nat) {
  out << "nature " << nat->name() << endl;
  out << "    access " << nat->access() << ";" << endl;
  out << "endnature" << endl;
}

void pform_dump(std::ostream &out, const ivl_discipline_s *dis) {
  out << "discipline " << dis->name() << endl;
  out << "    domain " << dis->domain() << ";" << endl;
  if (const ivl_nature_s *tmp = dis->potential())
    out << "    potential " << tmp->name() << ";" << endl;
  if (const ivl_nature_s *tmp = dis->flow())
    out << "    flow " << tmp->name() << ";" << endl;
  out << "enddiscipline" << endl;
}
