push!(LOAD_PATH, "../src")
using Satisfiability
using Test

__get_hash_name = Satisfiability.__get_hash_name

@testset "Individual SMTLIB2 statements" begin
    @satvariable(z1, Bool)
    @satvariable(z2[1:1], Bool)
    @satvariable(z12[1:1, 1:2], Bool)

    # indexed expression correctly declared
    @test smt(z12[1,2]) == "(declare-fun z12_1_2 () Bool)\n(assert z12_1_2)\n"
    #1d and 2d expression, with and without assert
    @test smt(z2) == "(declare-fun z2_1 () Bool)\n(assert z2_1)\n"
    @test smt(z12, assert=false) == "(declare-fun z12_1_1 () Bool)\n(declare-fun z12_1_2 () Bool)\n"

    # idea from https://microsoft.github.io/z3guide/docs/logic/propositional-logic
    # broadcast expression correctly generated
    hashname = __get_hash_name(:and, [z1, z2[1]], is_commutative=true)
    @test smt(z1 .∧ z2) == smt(z1, assert=false)*smt(z2, assert=false)*"(define-fun $hashname () Bool (and z1 z2_1))\n(assert $hashname)\n"
    
    # indexing creates a 1d expression
    hashname = __get_hash_name(:and, [z1, z12[1,2]], is_commutative=true)
    @test smt(z1 ∧ z12[1,2]) == smt(z1, assert=false)*smt(z12[1,2], assert=false)*"(define-fun $hashname () Bool (and z1 z12_1_2))\n(assert $hashname)\n"
    hashname = __get_hash_name(:and, z12, is_commutative=true)
    @test smt(z12[1,1] ∧ z12[1,2]) == smt(z12[1,1], assert=false)*smt(z12[1,2], assert=false)*"(define-fun $hashname () Bool (and z12_1_1 z12_1_2))\n(assert $hashname)\n"
    
    # all() and any() work
    hashname = __get_hash_name(:or, [z1 z12], is_commutative=true)
    @test smt(any(z1 .∨ z12)) == smt(z1, assert=false)*smt(z12, assert=false)*"(define-fun $hashname () Bool (or z1 z12_1_1 z12_1_2))\n(assert $hashname)\n"
    
    hashname = __get_hash_name(:and, [z1 z12], is_commutative=true)
    @test smt(all(z1 .∧ z12)) == smt(z1, assert=false)*smt(z12, assert=false)*"(define-fun $hashname () Bool (and z1 z12_1_1 z12_1_2))\n(assert $hashname)\n"
    
end

@testset "Generate additional exprs" begin
    @satvariable(z1, Bool)
    @satvariable(z12[1:1, 1:2], Bool)

    # implies, also tests \r\n
    hashname = __get_hash_name(:implies, [z1, z12[1,2]])
    @test smt(z1 ⟹ z12[1,2], line_ending="\r\n") == "(declare-fun z1 () Bool)\r\n(declare-fun z12_1_2 () Bool)\r\n(define-fun $hashname () Bool (=> z1 z12_1_2))\r\n(assert $hashname)\r\n"
    
    # iff, also tests \r\n
    hashname = __get_hash_name(:iff, [z1, z12[1,2]])
    @test smt(z1 ⟺ z12[1,2], line_ending="\r\n") == smt(z1, assert=false, line_ending="\r\n")*smt(z12[1,2], assert=false, line_ending="\r\n")*"(define-fun $hashname () Bool (= z1 z12_1_2))\r\n(assert $hashname)\r\n"
    
    # xor
    hashname = __get_hash_name(:xor, z12, is_commutative=true)
    @test smt(xor(z12[1,1], z12[1,2])) == smt(z12[1,1], assert=false)*smt(z12[1,2], assert=false)*"(define-fun $hashname () Bool (xor z12_1_1 z12_1_2))\n(assert $hashname)\n"
    
    # if-then-else
    @satvariable(x, Bool)
    @satvariable(y, Bool)
    @satvariable(z, Bool)
    hashname = __get_hash_name(:ite, [x,y,z])
    @test smt(ite(x,y,z)) == smt(x, assert=false)*smt(y, assert=false)*smt(z, assert=false)*"(define-fun $hashname () Bool (ite x y z))\n(assert $hashname)\n"
end

@testset "Generate nested expr without duplications" begin
    @satvariable(x, Bool)
    @satvariable(y, Bool)

    xyname = __get_hash_name(:and, [x,y], is_commutative=true)
    xy = and(x,y)
    yx = and(y,x)
    topname = __get_hash_name(:or, [xy], is_commutative=true)
    @test smt(or(xy, yx)) == smt(x, assert=false)*smt(y, assert=false)*
"(define-fun $xyname () Bool (and x y))
(define-fun $topname () Bool (or $xyname))
(assert $topname)\n"

    # Generate a nested expr with not (1-ary op) without duplicating statements
    xname = __get_hash_name(:not, [x])
    nx = ¬x
    xyname = __get_hash_name(:and, [nx], is_commutative=true)
    @test smt(and(¬x, ¬x)) == smt(x, assert=false)*
"(define-fun $xname () Bool (not x))
(define-fun $xyname () Bool (and $xname))
(assert $xyname)\n"
end

@testset "Generate SMT file" begin
    @satvariable(z1, Bool)
    @satvariable(z12[1:1, 1:2], Bool)
    
    save(z1 .∧ z12, "outfile")
    text = read(open("outfile.smt", "r"), String)
    @test text == smt(all(z1 .∧ z12))*"(check-sat)\n"
    @satvariable(a, Int)
    @test_logs (:warn, "Top-level expression must be Boolean to produce a valid SMT program.") match_mode=:any save(a)
end