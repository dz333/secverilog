
%{
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

# include "config.h"

# include  <iostream>

/*
 * This file implements synthesis based on matching threads and
 * converting them to equivalent devices. The trick here is that the
 * proc_match_t functor can be used to scan a process and generate a
 * string of tokens. That string of tokens can then be matched by the
 * rules to determine what kind of device is to be made.
 */

# include  "netlist.h"
# include  "netmisc.h"
# include  "functor.h"
# include  <cassert>

#pragma GCC diagnostic warning "-Wfree-nonheap-object"

struct syn_token_t {
      int token;

      NetAssignBase*assign;
      NetProcTop*top;
      NetEvWait*evwait;
      NetEvent*event;
      NetExpr*expr;

      syn_token_t*next_;
};
#define YYSTYPE syn_token_t*

static int yylex();
static void yyerror(const char*);
static Design*des_;

static void make_DFF_CE(Design*des, NetProcTop*top, NetEvWait*wclk,
			NetEvent*eclk, NetExpr*cexp, NetAssignBase*asn);
static void make_initializer(Design*des, NetProcTop*top, NetAssignBase*asn);

%}

%token S_ALWAYS S_ASSIGN S_ASSIGN_MEM S_ASSIGN_MUX S_ELSE S_EVENT
%token S_EXPR S_IF S_INITIAL

%%

start

  /* These rules match simple DFF devices. Clocked assignments are
     simply implemented as DFF, and a CE is easily expressed with a
     conditional statement. The typical Verilog that get these are:

     always @(posedge CLK) Q = D
     always @(negedge CLK) Q = D

     always @(posedge CLK) if (CE) Q = D;
     always @(negedge CLK) if (CE) Q = D;

     The width of Q and D cause a wide register to be created. The
     code generators generally implement that as an array of
     flip-flops. */

	: S_ALWAYS '@' '(' S_EVENT ')' S_ASSIGN ';'
		{ make_DFF_CE(des_, $1->top, $2->evwait, $4->event,
			      0, $6->assign);
		}

	| S_ALWAYS '@' '(' S_EVENT ')' S_IF S_EXPR S_ASSIGN ';' ';'
		{ make_DFF_CE(des_, $1->top, $2->evwait, $4->event,
			      $7->expr, $8->assign);
		}

  /* Unconditional assignments in initial blocks should be made into
     initializers wherever possible. */

	| S_INITIAL S_ASSIGN
		{ make_initializer(des_, $1->top, $2->assign);
		}

	;
%%


  /* Various actions. */

static void hookup_DFF_CE(NetFF*ff, NetESignal*d, NetEvProbe*pclk,
                          NetNet*ce, NetAssign_*a, unsigned rval_pinoffset)
{

	// a->sig() is a *NetNet, which doesn't have the loff_ and
	// lwid_ context.  Add the correction for loff_ ourselves.

	// This extra calculation allows for assignments like:
	//    lval[7:1] <= foo;
	// where lval is really a "reg [7:0]". In other words, part
	// selects in the l-value are handled by loff and the lwidth().

      connect(ff->pin_Data(), d->sig()->pin(0));
      connect(ff->pin_Q(), a->sig()->pin(0));

      connect(ff->pin_Clock(), pclk->pin(0));
      if (ce) connect(ff->pin_Enable(), ce->pin(0));

      ff->attribute(perm_string::literal("LPM_FFType"), verinum("DFF"));
      if (pclk->edge() == NetEvProbe::NEGEDGE)
	    ff->attribute(perm_string::literal("Clock:LPM_Polarity"), verinum("INVERT"));


	/* This lval_ represents a reg that is a WIRE in the
	   synthesized results. This function signals the destructor
	   to change the REG that this l-value refers to into a
	   WIRE. It is done then, at the last minute, so that pending
	   synthesis can continue to work with it as a WIRE. */
      a->turn_sig_to_wire_on_release();
}

static void make_DFF_CE(Design*des, NetProcTop*top, NetEvWait*wclk,
			NetEvent*eclk, NetExpr*cexp, NetAssignBase*asn)
{
      assert(asn);

      NetEvProbe*pclk = eclk->probe(0);
      NetESignal*d = dynamic_cast<NetESignal*> (asn->rval());
      NetNet*ce = cexp? cexp->synthesize(des, top->scope(), cexp) : 0;

      if (d == 0) {
	    cerr << asn->get_fileline() << ": internal error: "
		 << " not a simple signal? " << *asn->rval() << endl;
      }

      assert(d);

      NetAssign_*a;
      unsigned rval_pinoffset=0;
      for (unsigned i=0; (a=asn->l_val(i)); i++) {

	// asn->l_val(i) are the set of *NetAssign_'s that form the list
	// of lval expressions.  Treat each one independently, keeping
	// track of which bits of rval to use for each set of DFF inputs.
	// For example, given:
	//      {carry,data} <= x + y + z;
	// run through this loop twice, where a and rval_pinoffset are
	// first data and 0, then carry and 1.
	// FIXME:  ff gets its pin names wrong when loff_ is nonzero.

	    if (a->sig()) {
              // cerr << "new NetFF named " << a->name() << endl;
              NetFF*ff = new NetFF(top->scope(), a->name(),
				   a->sig()->vector_width());
              hookup_DFF_CE(ff, d, pclk, ce, a, rval_pinoffset);
              des->add_node(ff);
	    }
            rval_pinoffset += a->lwidth();
      }
      des->delete_process(top);
}

/*
 * An assignment in an initial statement is the same as giving the
 * nexus an initial value. For synthesized netlists, we can just set
 * the initial value for the link and get rid of the assignment
 * process.
 */
static void make_initializer(Design*des, NetProcTop*top, NetAssignBase*asn)
{
      NetESignal*rsig = dynamic_cast<NetESignal*> (asn->rval());
      assert(rsig);

      for (unsigned idx = 0 ;  idx < asn->l_val(0)->lwidth() ;  idx += 1) {

	    verinum::V bit = rsig->sig()->pin(idx).nexus()->driven_value();

	    Nexus*nex = asn->l_val(0)->sig()->pin(idx).nexus();
	    for (Link*cur = nex->first_nlink()
		       ;  cur ;  cur = cur->next_nlink()) {

		  if (dynamic_cast<NetNet*> (cur->get_obj()))
			cur->set_init(bit);

	    }
      }

      des->delete_process(top);
}

static syn_token_t*first_ = 0;
static syn_token_t*last_ = 0;
static syn_token_t*ptr_ = 0;

/*
 * The match class is used to take a process and turn it into a stream
 * of tokens. This stream is used by the yylex function to feed tokens
 * to the parser.
 */
struct tokenize : public proc_match_t {
      tokenize() { }
      ~tokenize() { }

      int assign(NetAssign*dev)
      {
	    syn_token_t*cur;
	    cur = new syn_token_t;
	    // Bit Muxes can't be synthesized (yet), but it's too much
	    // work to detect them now.
	    // cur->token = dev->l_val(0)->bmux() ? S_ASSIGN_MUX : S_ASSIGN;
	    cur->token = S_ASSIGN;
	    cur->assign = dev;
	    cur->next_ = 0;
	    last_->next_ = cur;
	    last_ = cur;
	    return 0;
      }

      int assign_nb(NetAssignNB*dev)
      {
	    syn_token_t*cur;
	    cur = new syn_token_t;
	    // Bit Muxes can't be synthesized (yet), but it's too much
	    // work to detect them now.
	    // cur->token = dev->l_val(0)->bmux() ? S_ASSIGN_MUX : S_ASSIGN;
	    cur->token = S_ASSIGN;
	    cur->assign = dev;
	    cur->next_ = 0;
	    last_->next_ = cur;
	    last_ = cur;
	    return 0;
      }

      int condit(NetCondit*dev)
      {
	    syn_token_t*cur;

	    cur = new syn_token_t;
	    cur->token = S_IF;
	    cur->next_ = 0;
	    last_->next_ = cur;
	    last_ = cur;

	    cur = new syn_token_t;
	    cur->token = S_EXPR;
	    cur->expr = dev->expr();
	    cur->next_ = 0;
	    last_->next_ = cur;
	    last_ = cur;

	    /* Because synthesis is broken this is needed to prevent
	     * a seg. fault. */
	    if (!dev->if_clause()) return 0;
	    dev -> if_clause() -> match_proc(this);

	    if (dev->else_clause()) {
		  cur = new syn_token_t;
		  cur->token = S_ELSE;
		  cur->next_ = 0;
		  last_->next_ = cur;
		  last_ = cur;

		  dev -> else_clause() -> match_proc(this);
	    }

	    cur = new syn_token_t;
	    cur->token = ';';
	    cur->next_ = 0;
	    last_->next_ = cur;
	    last_ = cur;
	    return 0;
      }

      int event_wait(NetEvWait*dev)
      {
	    syn_token_t*cur;

	    cur = new syn_token_t;
	    cur->token = '@';
	    cur->evwait = dev;
	    cur->next_ = 0;
	    last_->next_ = cur;
	    last_ = cur;

	    cur = new syn_token_t;
	    cur->token = '(';
	    cur->next_ = 0;
	    last_->next_ = cur;
	    last_ = cur;

	    for (unsigned idx = 0;  idx < dev->nevents(); idx += 1) {
		  cur = new syn_token_t;
		  cur->token = S_EVENT;
		  cur->event = dev->event(idx);
		  cur->next_ = 0;
		  last_->next_ = cur;
		  last_ = cur;
	    }

	    cur = new syn_token_t;
	    cur->token = ')';
	    cur->next_ = 0;
	    last_->next_ = cur;
	    last_ = cur;

	    dev -> statement() -> match_proc(this);

	    cur = new syn_token_t;
	    cur->token = ';';
	    cur->next_ = 0;
	    last_->next_ = cur;
	    last_ = cur;
	    return 0;
      }
};

static void syn_start_process(NetProcTop*t)
{
      first_ = new syn_token_t;
      last_ = first_;
      ptr_ = first_;

      first_->token = (t->type() == IVL_PR_ALWAYS)? S_ALWAYS : S_INITIAL;
      first_->top = t;
      first_->next_ = 0;

      tokenize go;
      t -> statement() -> match_proc(&go);
}

static void syn_done_process()
{
      while (first_) {
	    syn_token_t*cur = first_;
	    first_ = cur->next_;
	    delete cur;
      }
}

static int yylex()
{
      if (ptr_ == 0) {
	    yylval = 0;
	    return 0;
      }

      yylval = ptr_;
      ptr_ = ptr_->next_;
      return yylval->token;
}

struct syn_rules_f  : public functor_t {
      ~syn_rules_f() { }

      void process(class Design*des, class NetProcTop*top)
      {
	      /* If the scope that contains this process as a cell
		 attribute attached to it, then skip synthesis. */
	    if (top->scope()->attribute(perm_string::literal("ivl_synthesis_cell")).len() > 0)
		  return;

	    syn_start_process(top);
	    yyparse();
	    syn_done_process();
      }
};

void syn_rules(Design*d)
{
      des_ = d;
      syn_rules_f obj;
      des_->functor(&obj);
}

static void yyerror(const char*)
{
}
