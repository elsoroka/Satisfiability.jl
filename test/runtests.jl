using BooleanSatisfiability
using Test

# Constructing Boolean expressions
include("boolean_operation_tests.jl")

# Generating SMT expressions
include("smt_representation_tests.jl")

# Calling Z3 and interpreting the result
include("solver_interface_tests.jl")
