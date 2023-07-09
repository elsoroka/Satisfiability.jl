using BooleanSatisfiability
using Test

# assign is used after calling the solver so it belongs here.
@testset "Assign values" begin
    @satvariable(x[1:3], :Bool)
    @satvariable(y[1:2], :Bool)
    @satvariable(z, :Bool)
    
    prob = and(
        all(x),
        all(x .∨ [y; z]),
        all(¬y),
        z
    )
    values = Dict{String, Bool}("x_1" => 1,"x_2" => 1,"x_3" => 1,
              "y_1" => 0, "y_2" => 0,)
    BooleanSatisfiability.__assign!(prob, values)
    @test ismissing(value(z))
    @test all(value(x) .== [1, 1 ,1])
    @test all(value(y) .== [0, 0])
    

    # Creating a new expression where all children have assigned values also yields assigned values
    @test all(value(x .∨ [y; z]) .== 1) 
    @test value(and(prob.children[1], prob.children[2])) == 1

    
    # Test other assignments, especially reducing child values
    test_expr = BoolExpr(:XOR, x, nothing, "test")
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == false
    test_expr.op = :ITE
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == true
    test_expr = BoolExpr(:IMPLIES, y, nothing, "test")
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == true
    test_expr.op = :IFF
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == true

    # done with Booleans, now test Int assignments
    values = Dict("a_1"=>1, "a_2"=>2, "a_3"=>3)
    test_expr = IntExpr(:EQ, Int(2,"a"), nothing, "test")
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == false
    test_expr.op = :LT
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == true
    test_expr.op = :GT
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == false
    test_expr.op = :LEQ
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == true
    test_expr.op = :GEQ
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == false
    
    # Arithmetic operations
    test_expr = IntExpr(:ADD, Int(3,"a"), nothing, "test")
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == 6
    test_expr.op = :SUB
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == -4

    test_expr.op = :MUL
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == 6

    values = Dict("a_1"=>1., "a_2"=>2., "a_3"=>3.)
    test_expr = RealExpr(:DIV, Real(3,"a"), nothing, "test")
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == (1. / 2. / 3.)


end


@testset "Solving a SAT problem" begin
    @satvariable(x[1:3], :Bool)
    @satvariable(y[1:2], :Bool)
    @satvariable(z, :Bool)

    exprs = [
        all(x),
        x .∨ [y; z],
        all(¬y),
        z
    ]
    status = sat!(exprs...)
    @test status == :SAT
    @test value(z) == 1
    @test all(value(x) .== [1 1 1])
    @test all(value(y) .== [0 0])

    # problem is unsatisfiable
    status = sat!(exprs..., ¬z)
    @test status == :UNSAT

    @test isnothing(value(z))
    @test all(map(isnothing, value(x)))
    @test all(map(isnothing, value(y)))
end

@testset "Custom solver interactions" begin
    @satvariable(x[1:3], :Bool)
    @satvariable(y[1:2], :Bool)
    
    exprs = BoolExpr[
        all(x),
        all(x[1:2] .∨ y),
        all(¬y),
    ]
    input = smt(exprs...)*"(check-sat)\n"
    proc, pstdin, pstdout, pstderr = open_solver(Z3())
    output = send_command(pstdin, pstdout, input, is_done=nested_parens_match)
    @test output == "sat\n"
end