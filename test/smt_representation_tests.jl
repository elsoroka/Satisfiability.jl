using BooleanSatisfiability
using Test

@testset "Individual SMTLIB2 statements" begin
    z1 = Bool("z1")
    z2 = Bool(1, "z2")
    z12 = Bool(1,2, "z12")

    @test smt(z1) == "(declare-const z1 Bool)\n"
    @test smt(z2) == "(declare-const z2_1 Bool)\n"
    # indexed expression correctly declared
    @test smt(z12[1,2]) == "(declare-const z12_1_2 Bool)\n"
    # nd expression correctly declared
    @test smt(z12) == "(declare-const z12_1_1 Bool)\n(declare-const z12_1_2 Bool)\n"

    # declare 1D and 2D exprs
    @test BooleanSatisfiability.declare(z2) == "(declare-const z2_1 Bool)\n"
    @test BooleanSatisfiability.declare(z12) == "(declare-const z12_1_1 Bool)\n(declare-const z12_1_2 Bool)\n"

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

@testset "Generate SMT file" begin
    z1 = Bool("z1")
    z12 = Bool(1,2, "z12")

    save(z1 .∧ z12, "outfile")
    text = read(open("outfile.smt", "r"), String)
    @test text == smt(all(z1 .∧ z12))*"(check-sat)\n"
end