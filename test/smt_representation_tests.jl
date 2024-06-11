push!(LOAD_PATH, "../src")
using Satisfiability
using Test

@testset "Individual SMTLIB2 statements" begin
    @satvariable(β1, Bool)
    @satvariable(z2[1:1], Bool)
    @satvariable(z12[1:1, 1:2], Bool)

    # indexed expression correctly declared
    @test smt(z12[1,2]) == "(declare-fun z12_1_2 () Bool)\n(assert z12_1_2)\n"
    #1d and 2d expression, with and without assert
    @test smt(z2) == "(declare-fun z2_1 () Bool)\n(assert z2_1)\n"
    @test smt(z12, assert=false) == "(declare-fun z12_1_1 () Bool)\n(declare-fun z12_1_2 () Bool)\n"

    # idea from https://microsoft.github.io/z3guide/docs/logic/propositional-logic
    # broadcast expression correctly generated
    @test smt(β1 .∧ z2) == smt(z2, assert=false)*smt(β1, assert=false)*"(assert (and z2_1 $(Satisfiability.convert_to_ascii("β1"))))\n"
    
    # indexing creates a 1d expression
    @test smt(β1 ∧ z12[1,2]) == smt(z12[1,2], assert=false)*smt(β1, assert=false)*"(assert (and z12_1_2 $(Satisfiability.convert_to_ascii("β1"))))\n"

    @test smt(z12[1,1] ∧ z12[1,2]) == smt(z12[1,1], assert=false)*smt(z12[1,2], assert=false)*"(assert (and z12_1_1 z12_1_2))\n"
    
    # broadcast and and or
    @test smt(or(β1 .∨ z12)) == smt(z12, assert=false)*smt(β1, assert=false)*"(assert (or z12_1_1 z12_1_2 $(Satisfiability.convert_to_ascii("β1"))))\n"
    
    @test smt(and(β1 .∧ z12)) == smt(z12, assert=false)*smt(β1, assert=false)*"(assert (and z12_1_1 z12_1_2 $(Satisfiability.convert_to_ascii("β1"))))\n"
    
end

@testset "Generate additional exprs" begin
    @satvariable(z1, Bool)
    @satvariable(z12[1:1, 1:2], Bool)

    # implies, also tests \r\n
    @test smt(z1 ⟹ z12[1,2], line_ending="\r\n") == "(declare-fun z1 () Bool)\r\n(declare-fun z12_1_2 () Bool)\r\n(assert (=> z1 z12_1_2))\r\n"
    
    # iff, also tests \r\n
    @test smt(z1 ⟺ z12[1,2], line_ending="\r\n") == smt(z1, assert=false, line_ending="\r\n")*smt(z12[1,2], assert=false, line_ending="\r\n")*"(assert (= z1 z12_1_2))\r\n"
    
    # xor
    @test smt(xor(z12[1,1], z12[1,2])) == smt(z12[1,1], assert=false)*smt(z12[1,2], assert=false)*"(assert (xor z12_1_1 z12_1_2))\n"
    
    # if-then-else
    @satvariable(x, Bool)
    @satvariable(y, Bool)
    @satvariable(z, Bool)
    @test smt(ite(x,y,z)) == smt(x, assert=false)*smt(y, assert=false)*smt(z, assert=false)*"(assert (ite x y z))\n"
end

@testset "Generate nested expr without duplications" begin
    @satvariable(x, Bool)
    @satvariable(y, Bool)

    xy = and(x,y)
    yx = and(y,x)
    @test smt(or(xy, yx)) == smt(x, assert=false)*smt(y, assert=false)*"(assert (or (and x y)))\n"

    # Generate a nested expr with not (1-ary op) without duplicating statements
    nx = ¬x
    @test smt(and(¬x, ¬x)) == smt(x, assert=false)*
"(assert (and (not x)))\n"
end

@testset "Generate SMT file" begin
    @satvariable(z1, Bool)
    @satvariable(z12[1:1, 1:2], Bool)
    
    save(z1 .∧ z12, io=open("outfile.smt", "w"), check_sat=true)
    text = read(open("outfile.smt", "r"), String)
    @test text == smt(z1 .∧ z12)*"(check-sat)\n"
    @satvariable(a, Int)
    @test_logs (:warn, "Top-level expression must be Boolean to produce a valid SMT program.") match_mode=:any save(a, io=open("outfile.smt", "w"), check_sat=true)
end