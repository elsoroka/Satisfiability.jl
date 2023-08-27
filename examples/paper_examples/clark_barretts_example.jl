# This push!(LOAD_PATH, "../../src/")
using Satisfiability, BenchmarkTools

#=
This example is from Clark Barrett's SMT-Switch paper, presenting a new SMT API for C++.
The goal is to illustrate the differences between Satisfiability.jl and SMT-Switch.
=#

@satvariable(x, BitVector, 32)
@satvariable(y, BitVector, 32)
x0 = x[1:8]
y0 = y[1:8]
@uninterpreted(f, (BitVector, 32), (BitVector, 32))

# open an interactive solver
isolver = open(Z3())

# set options, I'm leaving out :incremental because it seems to not work in my system's Z3.
start_cmds = "(set-logic QF_UFBV)
(set-option :produce-models true)
(set-option :produce-unsat-assumptions true)"
send_command(isolver, start_cmds, dont_wait=true)

assert!(isolver, distinct(f(x), f(y)))
push!(isolver) # default push is 1
assert!(isolver, x0 == y0)

status, assignment = sat!(isolver)
println("x = $(assignment["x"])")

pop!(isolver) # default pop is 1

exprs = [
    x0 >= y0, # >= is unsigned comparison for BitVectors
    x & y >= x,
    x & y >= y,
]
status, assignment = sat!(isolver, exprs...) # check-sat-assuming exprs
result = send_command(isolver, "(get-unsat-assumptions)", is_done=nested_parens_match)
# a limitation of Satisfiability.jl is the user will have to interpret the unsat assumptions in SMT-LIB format.
println(result)
close(isolver)