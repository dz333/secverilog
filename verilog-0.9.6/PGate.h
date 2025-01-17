#ifndef __PGate_H
#define __PGate_H
/*
 * Copyright (c) 1998-2008 Stephen Williams (steve@icarus.com)
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

#include "LineInfo.h"
#include "PDelays.h"
#include "StringHeap.h"
#include "named.h"
#include "netlist.h"
#include "svector.h"
#include <map>
#include <string>
class PExpr;
class PUdp;
class Module;
class TypeEnv;
class SecType;
class SexpPrinter;
struct Predicate;

/*
 * A PGate represents a Verilog gate. The gate has a name and other
 * properties, and a set of pins that connect to wires. It is known at
 * the time a gate is constructed how many pins the gate has.
 *
 * This pins of a gate are connected to expressions. The elaboration
 * step will need to convert expressions to a network of gates in
 * order to elaborate expression inputs, but that can easily be done.
 *
 * The PGate base class also carries the strength0 and strength1
 * strengths for those gates where the driver[s] can be described by a
 * single strength pair. There is a strength of the 0 drive, and a
 * strength of the 1 drive.
 */
class PGate : public LineInfo {

public:
  enum strength_t { HIGHZ, WEAK, PULL, STRONG, SUPPLY };

  explicit PGate(perm_string name, svector<PExpr *> *pins,
                 const svector<PExpr *> *del);

  explicit PGate(perm_string name, svector<PExpr *> *pins, PExpr *del);

  explicit PGate(perm_string name, svector<PExpr *> *pins);

  virtual ~PGate();

  perm_string get_name() const { return name_; }

  // This evaluates the delays as far as possible, but returns
  // an expression, and do not signal errors.
  void eval_delays(Design *des, NetScope *scope, NetExpr *&rise_time,
                   NetExpr *&fall_time, NetExpr *&decay_time,
                   bool as_net_flag = false) const;

  unsigned pin_count() const { return pins_ ? pins_->count() : 0; }
  PExpr *pin(unsigned idx) const { return (*pins_)[idx]; }

  strength_t strength0() const;
  strength_t strength1() const;

  void strength0(strength_t);
  void strength1(strength_t);

  map<perm_string, PExpr *> attributes;

  virtual void dump(ostream &out, unsigned ind = 4) const;
  virtual void elaborate(Design *des, NetScope *scope) const;
  virtual void elaborate_scope(Design *des, NetScope *sc) const;
  virtual bool elaborate_sig(Design *des, NetScope *scope) const;

protected:
  const svector<PExpr *> &get_pins() const { return *pins_; }

  void dump_pins(ostream &out) const;
  void dump_delays(ostream &out) const;

private:
  perm_string name_;
  PDelays delay_;
  svector<PExpr *> *pins_;

  strength_t str0_, str1_;

private: // not implemented
  PGate(const PGate &);
  PGate &operator=(const PGate &);
};

/* A continuous assignment has a single output and a single input. The
   input is passed directly to the output. This is different from a
   BUF because elaboration may need to turn this into a vector of
   gates. */
class PGAssign : public PGate {

public:
  explicit PGAssign(svector<PExpr *> *pins);
  explicit PGAssign(svector<PExpr *> *pins, svector<PExpr *> *dels);
  ~PGAssign();

  void dump(ostream &out, unsigned ind = 4) const;
  virtual void elaborate(Design *des, NetScope *scope) const;
  virtual bool elaborate_sig(Design *des, NetScope *scope) const;
  void typecheck(SexpPrinter &, TypeEnv &env, Predicate pred,
                 set<perm_string> &s) const;
  void collect_index_exprs(set<perm_string> &exprs, TypeEnv &);
  bool collect_dep_invariants(SexpPrinter &printer, TypeEnv &env);

private:
};

/*
 * The Builtin class is specifically a gate with one of the builtin
 * types. The parser recognizes these types during parse. These types
 * have special properties that allow them to be treated specially.
 *
 * A PGBuiltin can be grouped into an array of devices. If this is
 * done, the msb_ and lsb_ are set to the indices of the array
 * range. Elaboration causes a gate to be created for each element of
 * the array, and a name will be generated for each gate.
 */
class PGBuiltin : public PGate {

public:
  enum Type {
    AND,
    NAND,
    OR,
    NOR,
    XOR,
    XNOR,
    BUF,
    BUFIF0,
    BUFIF1,
    NOT,
    NOTIF0,
    NOTIF1,
    PULLDOWN,
    PULLUP,
    NMOS,
    RNMOS,
    PMOS,
    RPMOS,
    CMOS,
    RCMOS,
    TRAN,
    RTRAN,
    TRANIF0,
    TRANIF1,
    RTRANIF0,
    RTRANIF1
  };

public:
  explicit PGBuiltin(Type t, perm_string name, svector<PExpr *> *pins,
                     svector<PExpr *> *del);
  explicit PGBuiltin(Type t, perm_string name, svector<PExpr *> *pins,
                     PExpr *del);
  ~PGBuiltin();

  Type type() const { return type_; }
  void set_range(PExpr *msb, PExpr *lsb);

  virtual void dump(ostream &out, unsigned ind = 4) const;
  virtual void elaborate(Design *, NetScope *scope) const;
  virtual bool elaborate_sig(Design *des, NetScope *scope) const;

private:
  unsigned calculate_array_count_(Design *, NetScope *, long &high,
                                  long &low) const;

  void calculate_gate_and_lval_count_(unsigned &gate_count,
                                      unsigned &lval_count) const;

  NetNode *create_gate_for_output_(Design *, NetScope *, perm_string gate_name,
                                   unsigned instance_width) const;

  Type type_;
  PExpr *msb_;
  PExpr *lsb_;
};

/*
 * This kind of gate is an instantiation of a module. The stored type
 * is the name of a module definition somewhere in the pform. This
 * type also handles UDP devices, because it is generally not known at
 * parse time whether a name belongs to a module or a UDP.
 */
class PGModule : public PGate {

public:
  // The name is the *instance* name of the gate.

  // If the binding of ports is by position, this constructor
  // builds everything all at once.
  explicit PGModule(perm_string type, perm_string name, svector<PExpr *> *pins);

  // If the binding of ports is by name, this constructor takes
  // the bindings and stores them for later elaboration.
  explicit PGModule(perm_string type, perm_string name, named<PExpr *> *pins,
                    unsigned npins);

  ~PGModule();

  // Parameter overrides can come as an ordered list, or a set
  // of named expressions.
  void set_parameters(svector<PExpr *> *o);
  void set_parameters(named<PExpr *> *pa, unsigned npa);
  perm_string get_pin_name(unsigned idx);
  PExpr *get_param(unsigned idx);
  unsigned get_pin_count();

  // Modules can be instantiated in ranges. The parser uses this
  // method to pass the range to the pform.
  void set_range(PExpr *msb, PExpr *lsb);

  virtual void fillPinMap(map<perm_string, perm_string> &pinSubst,
                          Module *moddef);
  virtual void fillParamMap(map<perm_string, perm_string> &paraSubst,
                            Module *moddef);
  virtual void dump(ostream &out, unsigned ind = 4) const;
  virtual void elaborate(Design *, NetScope *scope) const;
  virtual void elaborate_scope(Design *des, NetScope *sc) const;
  virtual bool elaborate_sig(Design *des, NetScope *scope) const;
  void typecheck(SexpPrinter &, TypeEnv &env,
                 map<perm_string, Module *> modules);

  // This returns the module name of this module. It is a
  // permallocated string.
  perm_string get_type();

private:
  perm_string type_;
  svector<PExpr *> *overrides_;
  named<PExpr *> *pins_;
  unsigned npins_;

  // These members support parameter override by name
  named<PExpr *> *parms_;
  unsigned nparms_;

  // Arrays of modules are give if these are set.
  PExpr *msb_;
  PExpr *lsb_;

  friend class delayed_elaborate_scope_mod_instances;
  void elaborate_mod_(Design *, Module *mod, NetScope *scope) const;
  void elaborate_udp_(Design *, PUdp *udp, NetScope *scope) const;
  void elaborate_scope_mod_(Design *des, Module *mod, NetScope *sc) const;
  void elaborate_scope_mod_instances_(Design *des, Module *mod,
                                      NetScope *sc) const;
  bool elaborate_sig_mod_(Design *des, NetScope *scope, Module *mod) const;
  bool elaborate_sig_udp_(Design *des, NetScope *scope, PUdp *udp) const;

  NetNet *resize_net_to_port_(Design *des, NetScope *scope, NetNet *sig,
                              unsigned port_wid, NetNet::PortType dir,
                              bool as_signed) const;
};

#endif
