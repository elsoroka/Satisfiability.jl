module BooleanSatisfiability

export AbstractExpr,
       BoolExpr,
       and, ∧,
       or,  ∨,
       not, ¬,
       implies, ⟹,
       value

export smt,
       declare,
       save

export sat!
       
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