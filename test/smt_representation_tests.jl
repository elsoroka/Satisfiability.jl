using BooleanSatisfiability
using Test

@testset "Individual SMTLIB2 statements" begin
    @satvariable(z1, Bool)
    @satvariable(z2[1:1], Bool)
    @satvariable(z12[1:1, 1:2], Bool)

    # indexed expression correctly declared
    @test smt(z12[1,2]) == "(declare-const z12_1_2 Bool)\n"
    #1d and 2d expression
    @test smt(z2) == "(declare-const z2_1 Bool)\n"
    @test smt(z12) == "(declare-const z12_1_1 Bool)\n(declare-const z12_1_2 Bool)\n"

    # idea from https://microsoft.github.io/z3guide/docs/logic/propositional-logic
    # broadcast expression correctly generated
    hashname = BooleanSatisfiability.__get_hash_name(:AND, [z1, z2[1]])
    @test smt(z1 .∧ z2) == smt(z1)*smt(z2)*"(define-fun $hashname () Bool (and z1 z2_1))\n(assert $hashname)\n"
    
    # indexing creates a 1d expression
    hashname = BooleanSatisfiability.__get_hash_name(:AND, [z1, z12[1,2]])
    @test smt(z1 ∧ z12[1,2]) == smt(z1)*smt(z12[1,2])*"(define-fun $hashname () Bool (and z1 z12_1_2))\n(assert $hashname)\n"
    hashname = BooleanSatisfiability.__get_hash_name(:AND, z12)
    @test smt(z12[1,1] ∧ z12[1,2]) == smt(z12[1,1])*smt(z12[1,2])*"(define-fun $hashname () Bool (and z12_1_1 z12_1_2))\n(assert $hashname)\n"
    
    # all() and any() work
    hashname = BooleanSatisfiability.__get_hash_name(:OR, [z1 z12])
    @test smt(any(z1 .∨ z12)) == smt(z1)*smt(z12)*"(define-fun $hashname () Bool (or z1 z12_1_1 z12_1_2))\n(assert $hashname)\n"
    
    hashname = BooleanSatisfiability.__get_hash_name(:AND, [z1 z12])
    @test smt(all(z1 .∧ z12)) == smt(z1)*smt(z12)*"(define-fun $hashname () Bool (and z1 z12_1_1 z12_1_2))\n(assert $hashname)\n"
    
    # cross all() and any() terms
    # TESTS DO NOT WORK
   # inner = z1.∨ z12
    #hashname = BooleanSatisfiability.__get_hash_name(:AND, inner)
    #@test smt(all(inner)) == smt(inner)*"(define-fun $hashname () Bool (and $(inner#[1].name) $(inner![2].name)))\n(assert $hashname)\n"

   # inner = z1.∧ z12
    #hashname = BooleanSatisfiability.__get_hash_name(:OR, inner)
    #@test smt(any(inner)) == smt(inner)*"(define-fun $hashname () Bool (or $(inner#[1].name) $(inner[2].name)))\n(assert $hashname)\n"
end

@testset "Generate additional exprs" begin
    @satvariable(z1, Bool)
    @satvariable(z12[1:1, 1:2], Bool)

    # implies, also tests \r\n
    hashname = BooleanSatisfiability.__get_hash_name(:IMPLIES, [z1, z12[1,2]])
    @test smt(z1 ⟹ z12[1,2], line_ending="\r\n") == "(declare-const z1 Bool)\r\n(declare-const z12_1_2 Bool)\r\n(define-fun $hashname () Bool (=> z1 z12_1_2))\r\n(assert $hashname)\r\n"
    
    # iff, also tests \r\n
    hashname = BooleanSatisfiability.__get_hash_name(:IFF, [z1, z12[1,2]])
    @test smt(z1 ⟺ z12[1,2], line_ending="\r\n") == smt(z1, line_ending="\r\n")*smt(z12[1,2], line_ending="\r\n")*"(define-fun $hashname () Bool (= z1 z12_1_2))\r\n(assert $hashname)\r\n"
    
    # xor
    hashname = BooleanSatisfiability.__get_hash_name(:XOR, z12)
    @test smt(xor(z12[1,1], z12[1,2])) == smt(z12[1,1])*smt(z12[1,2])*"(define-fun $hashname () Bool (xor z12_1_1 z12_1_2))\n(assert $hashname)\n"
    
    # if-then-else
    @satvariable(x, Bool)
    @satvariable(y, Bool)
    @satvariable(z, Bool)
    hashname = BooleanSatisfiability.__get_hash_name(:ITE, [x,y,z])
    @test smt(ite(x,y,z)) == smt(x)*smt(y)*smt(z)*"(define-fun $hashname () Bool (ite x y z))\n(assert $hashname)\n"
end

@testset "Generate nested expr without duplications" begin
    @satvariable(x, Bool)
    @satvariable(y, Bool)

    xyname = BooleanSatisfiability.__get_hash_name(:AND, [x,y])
    xy = and(x,y)
    yx = and(y,x)
    topname = BooleanSatisfiability.__get_hash_name(:OR, [xy, yx])
    @test smt(or(xy, yx)) == smt(x)*smt(y)*
"(define-fun $xyname () Bool (and x y))
(define-fun $topname () Bool (or $xyname $xyname))
(assert $topname)\n"

    # Generate a nested expr with not (1-ary op) without duplicating statements
    xname = BooleanSatisfiability.__get_hash_name(:NOT, [x])
    nx = ¬x
    xyname = BooleanSatisfiability.__get_hash_name(:AND, [nx, nx])
    @test smt(and(¬x, ¬x)) == smt(x)*
"(define-fun $xname () Bool (not x))
(define-fun $xyname () Bool (and $xname $xname))
(assert $xyname)\n"
end

@testset "Generate SMT file" begin
    @satvariable(z1, Bool)
    @satvariable(z12[1:1, 1:2], Bool)
    
    save(z1 .∧ z12, "outfile")
    text = read(open("outfile.smt", "r"), String)
    @test text == smt(all(z1 .∧ z12))*"(check-sat)\n"
    a = Int("a")
    @test_logs (:warn, "Top-level expression must be Boolean to produce a valid SMT program.") save(a+1)
end