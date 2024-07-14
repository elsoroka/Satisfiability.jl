push!(LOAD_PATH, "./src")
using Satisfiability
using Test, Logging

# assign is used after calling the solver so it belongs here.
@testset "Assign values" begin
    @satvariable(x[1:3], Bool)
    @satvariable(β[1:2], Bool)
    @satvariable(z, Bool)
    
    prob = and(
        and(x),
        and(x .∨ [β; z]),
        and(¬β)
    )
    values = Dict{String, Bool}("x_1" => 1,"x_2" => 1,"x_3" => 1,
              "β_1" => 0, "β_2" => 0,)
    @test_logs (:warn, "Value not found for variable z.") assign!(prob, values)
    @test ismissing(value(z))
    z.value = 0

    @test all(value(x) .== [1, 1 ,1])
    @test all(value(β) .== [0, 0])

    # Creating a new expression where all children have assigned values also yields assigned values
    @test all(value(x .∨ [β; z]) .== 1) 
    @test all(value(xor.(x, [β; z])) .== 1) 
    @test all(value(x .∧ [β; z]) .== 0) 
    @test value(and(prob.children[1], prob.children[2])) == 1

    
    # Test other assignments, especially reducing child values
    test_expr = BoolExpr(:xor, x, nothing, "test")
    assign!(test_expr, values)
    @test value(test_expr) == false
    test_expr.op = :ite
    assign!(test_expr, values)
    @test value(test_expr) == true
    test_expr = BoolExpr(:implies, β, nothing, "test")
    assign!(test_expr, values)
    @test value(test_expr) == true
    test_expr.op = :iff
    assign!(test_expr, values)
    @test value(test_expr) == true

    # done with Booleans, now test Int assignments
    values = Dict("a2_1"=>1, "a2_2"=>2, "a2_3"=>3)
    @satvariable(a2[1:2], Int)
    test_expr = IntExpr(:eq, a2, nothing, "test")
    assign!(test_expr, values)
    @test value(test_expr) == false
    test_expr.op = :lt
    assign!(test_expr, values)
    @test value(test_expr) == true
    test_expr.op = :gt
    assign!(test_expr, values)
    @test value(test_expr) == false
    test_expr.op = :leq
    assign!(test_expr, values)
    @test value(test_expr) == true
    test_expr.op = :geq
    assign!(test_expr, values)
    @test value(test_expr) == false
    
    # Arithmetic operations
    values = Dict("a3_1"=>1, "a3_2"=>2, "a3_3"=>3)
    @satvariable(a3[1:3], Int)
    test_expr = IntExpr(:add, a3, nothing, "test")
    assign!(test_expr, values)
    @test value(test_expr) == 6
    
    test_expr.op = :mul
    assign!(test_expr, values)
    @test value(test_expr) == 6

    test_expr.op = :sub; test_expr.children = test_expr.children[1:2]
    assign!(test_expr, values)
    @test value(test_expr) == -1

    test_expr.op = :div; test_expr.children = a3[2:3]
    assign!(test_expr, values)
    @test value(test_expr) == div(2,3)

    test_expr.op = :mod; test_expr.children = a3[2:3]
    assign!(test_expr, values)
    @test value(test_expr) == mod(2,3)
    
    values = Dict("a3_1"=>1, "a3_2"=>-2, "a3_3"=>3)
    test_expr.op = :abs; test_expr.children = a3[2:2]
    assign!(test_expr, values)
    @test value(test_expr) == 2 && value(a3[2]) == -2

    values = Dict("ar2_1"=>1., "ar2_2"=>2.)
    @satvariable(ar2[1:2], Real)
    test_expr = RealExpr(:rdiv, ar2, nothing, "test")
    assign!(test_expr, values)
    @test value(test_expr) == (1. / 2.)

    # Can't assign nonexistent operator
    #test_expr = RealExpr(:fakeop, Real(1,"a"), nothing, "test")
    #@test_logs (:error, "Unknown operator fakeop") assign!(test_expr, values)

    # Missing value assigned to missing
    @satvariable(b, Int)
    @test_logs (:warn, "Value not found for variable b.") ismissing(assign!(b, values))
end


@testset "Solving a SAT problem" begin

    @satvariable(x[1:3], Bool)
    @satvariable(y[1:2], Bool)
    @satvariable(z, Bool)

    exprs = BoolExpr[
        and(x),
        and(x .∨ [y; z]),
        and(¬y),
        z
    ]
    # other checks
    @test CVC5().name == "CVC5" # can initialize CVC5
    @test_throws ErrorException sat!(exprs, solver=Yices()) # this is because Yices requires setting a logic, users should do sat!(exprs, solver=Yices(), logic="logic)

    status = sat!(exprs, solver=Z3())
    @test status == :SAT
    @test value(z) == 1
    @test all(value(x) .== [1 1 1])
    @test all(value(y) .== [0 0])
    
    # Problem comes from a file
    save(exprs, io=open("testfile.smt", "w"))
    sat!(open("testfile.smt", "r"), solver=Z3())
    @test status == :SAT

    # dispatch on filename, open the file in sat!
    sat!("testfile.smt", solver=Z3())
    @test status == :SAT


    # problem is unsatisfiable
    status = sat!(exprs..., ¬z, solver=Z3())
    @test status == :UNSAT

    @test isnothing(value(z))
    @test all(map(isnothing, value(x)))
    @test all(map(isnothing, value(y)))

    # doesn't solve empty problem
    @test_throws(ErrorException, sat!(solver=Z3()))
end

@testset "Solving an integer-valued problem" begin
    CLEAR_VARNAMES!()
    @satvariable(a, Int)
    @satvariable(b, Int)
    expr1 = a + b + 2
    @test smt(expr1, assert=false) == "(declare-fun a () Int)
(declare-fun b () Int)
(define-fun add_99dce5c325207b7 () Int (+ a b 2))\n"
    
    expr = and(expr1 <= a, b + 1 >= b)
    result = "(declare-fun b () Int)
(declare-fun a () Int)
(assert (and (>= (+ b 1) b) (<= (+ a b 2) a)))\n"
    @test smt(expr) == result
    
    status = sat!(expr, solver=Z3(), logic="QF_LIA")
    @test status == :SAT
    @test value(a) == 0
    @test value(b) == -2
    
end

#
@testset "Custom solver interactions" begin
    @satvariable(x[1:3], Bool)
    @satvariable(y[1:2], Bool)
    
    exprs = BoolExpr[
        and(x),
        and(x[1:2] .∨ y),
        and(¬y),
    ]
    line_ending = Sys.iswindows() ? "\r\n" : "\n"
    input = smt(exprs...)*"(check-sat)$line_ending"

    # Set up a custom solver that doesn't work (it should be z3)
    if !Sys.iswindows() # this test doesn't work on Windows, probably because Windows cmd sucks
        solver = Solver("Z3", `Z3 -smt2 -in`)
        @test_throws Base.IOError open(solver)
    end

    # Interact using send_command
    interactive_solver = open(Z3())

    # can't check sat with no assertions
    std_ = stderr
    redirect_stderr(devnull)
    status, values = sat!(interactive_solver)
    @test status == :ERROR && Dict{String, Any}() == values
    redirect_stderr(std_)

    output = send_command(interactive_solver, input, is_done=is_sat_or_unsat)
    @test strip(output) == "sat"
    output = send_command(interactive_solver, "(get-model)", is_done=nested_parens_match)
    dict = parse_model(output)
    @test dict["x_1"] == true && dict["y_1"] == false

    # Pop and push assertion levels
    @test isnothing(push!(interactive_solver, 1)) # returns no output
    @test_throws ErrorException pop!(interactive_solver, 10) # can't pop too many levels
    @test isnothing(pop!(interactive_solver, 1)) # returns no output
    @test_throws ErrorException push!(interactive_solver, -1) # cannot push negative levels

    # Set and get options
    #result = get_option(interactive_solver, "produce-assertions")
    #@test result == "true" || result == "false"
    #result = set_option(interactive_solver, "incremental", true)
    #println("got response $result")

    # Check-sat-assuming
    status, assignment = sat!(interactive_solver)
    @test status == :SAT
    @test assignment["x_1"] == true && assignment["y_1"] == false
    
    # can assign values returned from sat!
    map( (e) -> assign!(e, assignment), exprs)
    @test all(value(x) .== [1 1 1])
    @test all(value(y) .== [0 0])

    # Practical application: Are there more solutions to this problem?
    push!(interactive_solver, 1)
    assert!(interactive_solver, distinct.(x, value(x)))
    status, assignment = sat!(interactive_solver, distinct.(y, value(y)))
    # but there isn't one so we get UNSAT
    @test status == :UNSAT
    # since it failed, we pop the offending assertions off
    pop!(interactive_solver, 1)

    # now calling sat gives us the original solution
    status, assignment = sat!(interactive_solver)
    map( (e) -> assign!(e, assignment), exprs)
    @test all(value(x) .== [1 1 1])
    @test all(value(y) .== [0 0])

    # can reset
    reset_assertions!(interactive_solver)
    @test interactive_solver.command_history[end] == "(reset-assertions)"
    reset!(interactive_solver)
    @test length(interactive_solver.command_history) == 1 # because of (reset)
    close(interactive_solver)
end
