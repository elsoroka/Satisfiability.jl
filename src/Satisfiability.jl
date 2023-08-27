module Satisfiability

export AbstractExpr,
       BoolExpr,
       IntExpr,
       UninterpretedFunc,
       @satvariable,
       @uninterpreted,
       RealExpr,
       AbstractBitVectorExpr,
       BitVectorExpr,
       isequal,
       hash, # required by isequal (?)
       in # specialize to use isequal instead of ==

export
       and, ∧,
       or,  ∨,
       not, ¬,
       implies, ⟹,
       xor, ⊻,
       iff, ⟺,
       ite,
       value
       
export
       ==, <, <=, >, >=,
       distinct
export
       +, -, *, /

# BitVector specific functions
export
    nextsize,
    bitcount,
    div,
    urem,
    <<,
    >>,
    >>>,
    &, |, ~,
    srem,
    smod,
    nor, ⊽,
    nand, ⊼,
    xnor,
    slt, sle,
    sgt, sge,
    concat,
    bv2int, int2bv,
    bvconst

export smt,
       save

export Solver,
       InteractiveSolver,
       Z3,
       CVC5,
       sat!,
       send_command,
       open, close,
       push, pop,
       assert!,
       #set_option!, get_option,
       nested_parens_match, is_sat_or_unsat,
       parse_model,
       assign!,
       reset!, reset_assertions!

# This tells us how to invoke the solvers
DEFAULT_SOLVER_CMDS = Dict(
    :Z3 => `z3 -smt2 -in`
)

#=  INCLUDES
    * BoolExpr.jl (definition of BoolExpr)
    * utilities.jl (internal, no public-facing functions)
    * Logical operators and, or, not, implies, distinct, xor
=#
include("BooleanOperations.jl")

#= INCLUDES
    * Declarations for IntExpr and RealExpr
    * Operations for IntExpr and RealExpr
=#
include("IntExpr.jl")

include("BitVectorExpr.jl")

include("uninterpreted_func.jl")

# include @satvariable later because we need some functions from BitVector to declare that type
include("smt_macros.jl")
include("multiple_dispatch_ops.jl")

__EXPR_TYPES = [BoolExpr, RealExpr, IntExpr, BitVectorExpr]

# Track the user-declared BoolExpr names so the user doesn't make duplicates.
# This will NOT contain hash names. If the user declares x = Bool("x"); y = Bool("y"); xy = and(x,y)
# GLOBAL_VARNAMES will contain "x" and "y", but not __get_hash_name(:AND, [x,y], is_commutative=true).
global GLOBAL_VARNAMES = Dict(t => String[] for t in __EXPR_TYPES)
# When false, no warnings will be issued
global WARN_DUPLICATE_NAMES = false

SET_DUPLICATE_NAME_WARNING!(value::Bool) = global WARN_DUPLICATE_NAMES = value

# this might be useful when solving something in a loop
CLEAR_VARNAMES!() = global GLOBAL_VARNAMES = Dict(t => String[] for t in __EXPR_TYPES)

export GLOBAL_VARNAMES,
       SET_DUPLICATE_NAME_WARNING!,
       CLEAR_VARNAMES!

#=  INCLUDES
    * declare (generate SMT variable declarations for expression)
    * smt (generate SMT representation of problem)
=#
include("smt_representation.jl")

#=  INCLUDES
    * sat! (solve problem)
    * sat.jl includes call_solver.jl
=#
include("sat.jl")

# Module end
end