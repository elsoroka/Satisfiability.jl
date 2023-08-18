using BooleanSatisfiability
using Test, Logging

# assign is used after calling the solver so it belongs here.
@testset "Assign values" begin
    @satvariable(x[1:3], Bool)
    @satvariable(y[1:2], Bool)
    @satvariable(z, Bool)
    
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
    z.value = 0

    @test all(value(x) .== [1, 1 ,1])
    @test all(value(y) .== [0, 0])

    # Creating a new expression where all children have assigned values also yields assigned values
    @test all(value(x .∨ [y; z]) .== 1) 
    @test all(value(xor.(x, [y; z])) .== 1) 
    @test all(value(x .∧ [y; z]) .== 0) 
    @test value(and(prob.children[1], prob.children[2])) == 1

    
    # Test other assignments, especially reducing child values
    test_expr = BoolExpr(:xor, x, nothing, "test")
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == false
    test_expr.op = :ite
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == true
    test_expr = BoolExpr(:implies, y, nothing, "test")
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == true
    test_expr.op = :iff
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == true

    # done with Booleans, now test Int assignments
    values = Dict("a2_1"=>1, "a2_2"=>2, "a2_3"=>3)
    @satvariable(a2[1:2], Int)
    test_expr = IntExpr(:eq, a2, nothing, "test")
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == false
    test_expr.op = :lt
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == true
    test_expr.op = :gt
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == false
    test_expr.op = :leq
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == true
    test_expr.op = :geq
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == false
    
    # Arithmetic operations
    values = Dict("a3_1"=>1, "a3_2"=>2, "a3_3"=>3)
    @satvariable(a3[1:3], Int)
    test_expr = IntExpr(:add, a3, nothing, "test")
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == 6
    
    test_expr.op = :mul
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == 6

    test_expr.op = :sub; test_expr.children = test_expr.children[1:2]
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == -1

    values = Dict("ar2_1"=>1., "ar2_2"=>2.)
    @satvariable(ar2[1:2], Real)
    test_expr = RealExpr(:div, ar2, nothing, "test")
    BooleanSatisfiability.__assign!(test_expr, values)
    @test value(test_expr) == (1. / 2.)

    # Can't assign nonexistent operator
    #test_expr = RealExpr(:fakeop, Real(1,"a"), nothing, "test")
    #@test_logs (:error, "Unknown operator fakeop") BooleanSatisfiability.__assign!(test_expr, values)

    # Missing value assigned to missing
    @satvariable(b, Int)
    @test ismissing(BooleanSatisfiability.__assign!(b, values))
end


@testset "Solving a SAT problem" begin
    # can initialize cvc5
    s = CVC5()

    @satvariable(x[1:3], Bool)
    @satvariable(y[1:2], Bool)
    @satvariable(z, Bool)

    exprs = BoolExpr[
        all(x),
        all(x .∨ [y; z]),
        all(¬y),
        z
    ]
    status = sat!(exprs, solver=Z3())
    @test status == :SAT
    @test value(z) == 1
    @test all(value(x) .== [1 1 1])
    @test all(value(y) .== [0 0])

    # problem is unsatisfiable
    status = sat!(exprs..., ¬z, solver=Z3())
    @test status == :UNSAT

    @test isnothing(value(z))
    @test all(map(isnothing, value(x)))
    @test all(map(isnothing, value(y)))
end

@testset "Solving an integer-valued problem" begin
    CLEAR_VARNAMES!()
    @satvariable(a, Int)
    @satvariable(b, Int)
    expr1 = a + b + 2
    @test smt(expr1, assert=false) == "(declare-fun a () Int)
(declare-fun b () Int)
(define-fun add_99dce5c325207b7 () Int (+ 2 a b))\n"
    
    expr = and(expr1 <= a, b + 1 >= b)
    result = "(declare-fun b () Int)
(declare-fun a () Int)
(define-fun add_f0a93f0b97da1ab2 () Int (+ 1 b))
(define-fun geq_e1bd460e008a4d8b () Bool (>= add_f0a93f0b97da1ab2 b))
(define-fun add_99dce5c325207b7 () Int (+ 2 a b))
(define-fun leq_a64c028ce18b2942 () Bool (<= add_99dce5c325207b7 a))
(define-fun and_79376630b5dc2f7c () Bool (and geq_e1bd460e008a4d8b leq_a64c028ce18b2942))
(assert and_79376630b5dc2f7c)\n"
    @test smt(expr) == result
    
    status = sat!(expr)
    @test status == :SAT
    @test value(a) == 0
    @test value(b) == -2
    
end

@testset "Custom solver interactions" begin
    @satvariable(x[1:3], Bool)
    @satvariable(y[1:2], Bool)
    
    exprs = BoolExpr[
        all(x),
        all(x[1:2] .∨ y),
        all(¬y),
    ]
    line_ending = Sys.iswindows() ? "\r\n" : "\n"
    input = smt(exprs...)*"(check-sat)$line_ending"

    # Set up a custom solver that doesn't work (it should be z3)
    if !Sys.iswindows() # this test doesn't work on Windows, probably because Windows cmd sucks
        solver = Solver("Z3", `Z3 -smt2 -in`)
        @test_throws Base.IOError open_solver(solver)
    end

    # Interact using send_command
    proc, pstdin, pstdout, pstderr = open_solver(Z3())
    output = send_command(pstdin, pstdout, input, is_done=nested_parens_match)
    @test output == "sat$line_ending"
end