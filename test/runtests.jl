using BooleanSatisfiability
using Test
import Pkg; Pkg.add("Logging")
using Logging

# Constructing Boolean expressions
include("boolean_operation_tests.jl")

# Constructiong Int and Real exprs
include("int_real_tests.jl")

# Generating SMT expressions
include("smt_representation_tests.jl")

# Calling Z3 and interpreting the result
include("solver_interface_tests.jl")

# Test with int and real problems
include("int_parse_tests.jl")

# Extra: Check that defining duplicate variables yields a warning
@testset "Duplicate variable warning" begin
    SET_DUPLICATE_NAME_WARNING!(true)
    z = Bool("z")
    @test_logs (:warn, "Duplicate variable name z of type Bool") Bool("z")
    
    # now we should have no warnings
    SET_DUPLICATE_NAME_WARNING!(false)
    @test_logs min_level=Logging.Warn Bool("z")
    
    # we can also clear the list
    SET_DUPLICATE_NAME_WARNING!(true)
    CLEAR_VARNAMES!()
    @test_logs min_level=Logging.Warn Bool("z")
end