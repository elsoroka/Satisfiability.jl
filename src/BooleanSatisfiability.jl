module BooleanSatisfiability

export AbstractExpr,
       BoolExpr,
       and, ∧,
       or,  ∨,
       not, ¬,
       implies, ⟹,
       xor, ⊻,
       iff, ⟺,
       ite,
       value

export smt,
       save

export sat!

# This tells us how to invoke the solvers
DEFAULT_SOLVER_CMDS = Dict(
    :Z3 => `z3 -smt2 -in`
)
       
#=  INCLUDES
    * BoolExpr.jl (definition of BoolExpr)
    * utilities.jl (internal, no public-facing functions)
    * Logical operators and, or, not, implies
    * Logical operators any and all
=#
include("BooleanOperations.jl")

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