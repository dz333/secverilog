#ifndef __AStatement_H
#define __AStatement_H
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

#include "LineInfo.h"
#include "PExpr.h"
#include "Statement.h"
#include "StringHeap.h"
#include "ivl_target.h"
#include <map>

class PExpr;
class NetAnalog;
class NetScope;
class Design;
class Predicate;

/*
 * A contribution statement is like an assignment: there is an l-value
 * expression and an r-value expression. The l-value is a branch probe
 * expression.
 */
class AContrib : public Statement {

public:
  AContrib(PExpr *lval, PExpr *rval);
  ~AContrib();

  virtual void dump(ostream &out, unsigned ind) const;
  virtual void typecheck(SexpPrinter &, TypeEnv &env, Predicate &pred,
                         set<perm_string> &defAssgn) const;
  void absintp(Predicate &) const;

  virtual NetProc *elaborate(Design *des, NetScope *scope) const;

private:
  PExpr *lval_;
  PExpr *rval_;
};

/*
 * An analog process is not a statement, but contains an analog
 * statement. The process is where we attach process characteristics
 * such as initial vs. always, attributes....
 */
class AProcess : public LineInfo {

public:
  AProcess(ivl_process_type_t t, Statement *st) : type_(t), statement_(st) {}

  ~AProcess();

  bool elaborate(Design *des, NetScope *scope) const;

  ivl_process_type_t type() const { return type_; }
  Statement *statement() { return statement_; }

  map<perm_string, PExpr *> attributes;

  // Dump the analog process
  void dump(ostream &out, unsigned ind) const;

private:
  ivl_process_type_t type_;
  Statement *statement_;

private: // not implemented
  AProcess(const AProcess &);
  AProcess &operator=(const AProcess &);
};

#endif
