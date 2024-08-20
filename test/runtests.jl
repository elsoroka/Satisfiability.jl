push!(LOAD_PATH, "../../src")
push!(LOAD_PATH, "./")
using Satisfiability
using Test, Logging

normalize_endings(s::String) = replace(s, "\r\n" => "\n")
Base.isapprox(str1::String, str2::String) = normalize_endings(str1) == normalize_endings(str2)

SET_DUPLICATE_NAME_WARNING!(false)
CLEAR_VARNAMES!()

# Constructing Boolean expressions
include("boolean_operation_tests.jl")

# Constructiong Int and Real exprs
include("int_real_tests.jl")

# Generating SMT expressionsexit()
include("smt_representation_tests.jl")

# Calling Z3 and interpreting the result
include("solver_interface_tests.jl")

# Test with int and real problems
include("output_parse_tests.jl")

include("bitvector_tests.jl")

include("ufunc_tests.jl")

# Extra: Check that defining duplicate variables yields a warning
@info("Check that redefining a variable yields a warning. One warning will be emitted.")
@testset "Duplicate variable warning" begin
    SET_DUPLICATE_NAME_WARNING!(true)
    @satvariable(z, Bool)
    @test_logs (:warn, "Duplicate variable name z of type Bool") @satvariable(z, Bool)

    # now we should have no warnings
    SET_DUPLICATE_NAME_WARNING!(false)
    @test_logs min_level = Logging.Warn @satvariable(z, Bool)

    # we can also clear the list
    SET_DUPLICATE_NAME_WARNING!(true)
    CLEAR_VARNAMES!()
    @test_logs min_level = Logging.Warn @satvariable(z, Bool)
    SET_DUPLICATE_NAME_WARNING!(false)
end

include("README_tests.jl")