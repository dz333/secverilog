SHELL := /bin/bash
BENCHS=$(shell ls *.v)

BENCH_EXP=$(BENCHS:.v=.expected)
BENCH_SMT=$(BENCHS:.v=.z3)
BENCH_OUT=$(BENCHS:.v=.out)
BENCH_DIFF=$(BENCHS:.v=.diff)
BENCH_LATTICE=$(BENCHS:.v=.lattice)
BENCH_FUN=$(BENCHS:.v=.fun)



all: $(BENCH_DIFF)
	@echo "All Tests passed!"

.PRECIOUS: %.z3 %.out

z3files: $(BENCH_SMT)

%.z3: %.v %.lattice %.fun ../verilog-0.9.6/ivl
	@echo "Generating $@"
	@../bin/iverilog -F $*.fun -l $*.lattice -z $*.v

%.out: %.z3
	@echo "Generating $@"
	@z3 -smt2 sat.smt=true -T:30 -t:20000 $< | grep "sat\|unknown\|error" > $@

%.diff: %.out %.expected
	@echo "Checking Diff"
	@diff $*.expected $<

.PHONY: clean
clean:
	@rm -rf *.out *.z3


