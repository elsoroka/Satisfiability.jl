using BooleanSatisfiability
using Test

@testset "Construct variables" begin
    # Write your tests here.
    z1 = Bool("z1")
    @test isa(z1,BoolExpr)
    
    z32 = Bool(3,2, "z32")
    @test isa(z32,Array{BoolExpr})
    @test size(z32) == (3,2)

    z23 = Bool(2,3, "z23")

    # Sizes are broadcastable
    z12 = Bool(1,2, "z12")
    z21 = Bool(2,1, "z21")
    # (1,) broadcasts with (1,2)
    @test all(size(z1 .∨ z12) .== (1,2))
    # (1,) broadcasts with (2,3)
    @test all(size(z1 .∨ z32) .== (3,2))
    # (1,2) broadcasts with (3,2)
    @test all(size(z12 .∧ z32) .== (3,2))
    # (2,1) broadcasts with (2,3)
    @test all(size(z21 .∧ z23) .== (2,3))

    # Wrong sizes aren't broadcastable
    # (1,2) doesn't broadcast with (2,3)
    @test_throws DimensionMismatch z12 .∧ z23
    # (2,3) doesn't broadcast with (3,2)
    @test_throws DimensionMismatch z32 .∨ z23

    # Nested wrong sizes also aren't broadcastable
    @test_throws DimensionMismatch (z1.∨z23) .∨ z32
end

@testset "Logical operations" begin
    z1 = Bool(1, "z1")
    z12 = Bool(1,2, "z12")
    z32 = Bool(3,2, "z32")
    z23 = Bool(2,3, "z23")

    # and(z) = z and or(z) = z
    @test and([z1[1]]) == z1[1]
    
    @test or([z23[1]]) == z23[1]
    
	# Can construct with 2 exprs
    @test all( (z1 .∧ z32)[1].children .== [z1[1], z32[1]] )
    @test  (z1 .∧ z32)[1].name == "and_z1_1...z32_1_1"
    @test all( (z1 .∨ z32)[2,1].children .== [z1[1], z32[2,1]] )
    @test  (z1 .∨ z32)[1].name == "or_z1_1...z32_1_1"

    # Can construct with N>2 exprs
    or_N = or.(z1, z12, z32)
    and_N = and.(z1, z12, z32)

    @test all( or_N[3,2].children .== [z1[1], z12[1,2], z32[3,2]] ) 
    @test  and_N[1].name == "and_z1_1...z32_1_1"

    @test all( or_N[1].children .== [z1[1], z12[1], z32[1]] ) 
	@test or_N[1].name == "or_z1_1...z32_1_1"
    
    # Can construct negation
    @test (¬z32)[1].children == [z32[1]]
    @test (¬z32)[1].name == "!z32_1_1"

    # Can construct Implies
    @test all((z1 .⟹ z23) .== (z23 .∨(¬z1)))
 
    # Can construct all() and any() statements
    @test any(z1 .∨ z12) == BoolExpr(:Or,  [z1[1], z12[1,1], z12[1,2]], nothing, "or_z1_z12")
    @test all(z1 .∧ z12) == BoolExpr(:And, [z1[1], z12[1,1], z12[1,2]], nothing, "and_z1_z12")
end

@testset "Individual SMTLIB2 statements" begin
    z1 = Bool("z1")
    z2 = Bool(1, "z2")
    z12 = Bool(1,2, "z12")
#    z23 = Bool(2,3, "z23")

    @test smt(z1) == "(declare-const z1 Bool)\n"
    @test smt(z2) == "(declare-const z2_1 Bool)\n"
    # indexed expression correctly declared
    @test smt(z12[1,2]) == "(declare-const z12_1_2 Bool)\n"
    # nd expression correctly declared
    @test smt(z12) == "(declare-const z12_1_1 Bool)\n(declare-const z12_1_2 Bool)\n"
    # idea from https://microsoft.github.io/z3guide/docs/logic/propositional-logic
    # broadcast expression correctly generated
    @test smt(z1 .∧ z2) == smt(z1)*smt(z2)*"(define-fun and_z1_z2_1 () Bool (and z1 z2_1))\n(assert (and_z1_z2_1))\n"
    
    # indexing creates a 1d expression
    @test smt(z1 ∧ z12[1,2]) == smt(z1)*smt(z12[1,2])*"(define-fun and_z1_z12_1_2 () Bool (and z1 z12_1_2))\n(assert (and_z1_z12_1_2))\n"
    @test smt(z12[1,1] ∧ z12[1,2]) == smt(z12[1,1])*smt(z12[1,2])*"(define-fun and_z12_1_1_z12_1_2 () Bool (and z12_1_1 z12_1_2))\n(assert (and_z12_1_1_z12_1_2))\n"
    
    # any(1d expression) = single expression
    println(smt(any(z1 .∨ z12)))
    println(smt(z1)*smt(z12)*"(define-fun or_z1_z12 () Bool (or z1 z12_1_1 z12_1_2))\n(assert (or_z1_z12))\n")
    @test smt(any(z1 .∨ z12)) == smt(z1)*smt(z12)*"(define-fun or_z1_z12 () Bool (or z1 z12_1_1 z12_1_2))\n(assert (or_z1_z12))\n"
    
    # all(nd expression) works
    println(smt(all(z1 .∧ z12)))
    println(smt(z1)*smt(z12)*"(define-fun and_z1_z12 () Bool (and (z1 z12_1_1 z12_1_2)))\n(assert (and_z1_z12))\n")
    @test smt(all(z1 .∧ z12)) == smt(z1)*smt(z12)*"(define-fun and_z1_z12 () Bool (and (z1 z12_1_1 z12_1_2)))\n(assert (and_z1_z12))\n"
    @test smt(all(z1 .∨ z12)) == smt(z1)*smt(z12)*"(define-fun or_z1_z12 () Bool (or (z1 z12_1_1 z12_1_2)))\n(assert (or_z1_z12))\n"

end

# TODO 4/26/23
# Fix names (just add them for now) - done 4/28/23
# Fix equality comparison - done 4/28/23
# Start SMTLIB2 section - done 4/30/23

# TODO 5/1/23
# Fix broadcasting ambiguity - done 5/6/23
# Finish unit tests for operators  - done 5/6/23
# Add docstrings to all functions
# Add return types to all functions - resolved, not necessary. 5/6/23
# Clean up export list

# TODO 5/6/23
# Change to arrays of 1-valued BoolExpr - done 5/6/23
# Implement all(z1 .∧ z2) and any(z1 .∨ z2) behavior
# Fix SMT statement functions after change - done

# TODO 5/12/23
# Fix naming to be more coherent, for example using hashing to generate unique hex names for combined operators
