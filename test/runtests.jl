using BooleanSatisfiability
using Test

@testset "Construct variables" begin
    # Write your tests here.
    z1 = Bool(1)
    @test size(z1) == (1,)
    z32 = Bool(3,2)
    @test size(z32) == (3,2)
    z23 = Bool(2,3)

    # Sizes are broadcastable
    z12 = Bool(1,2)
    z21 = Bool(2,1)
    # (1,) broadcasts with (1,2)
    @test all(size(z1 ∨ z12) .== (1,2))
    # (1,) broadcasts with (2,3)
    @test all(size(z1 ∨ z32) .== (3,2))
    # (1,2) broadcasts with (3,2)
    @test all(size(z12 ∧ z32) .== (3,2))
    # (2,1) broadcasts with (2,3)
    @test all(size(z21 ∧ z23) .== (2,3))

    # Wrong sizes aren't broadcastable
    # (1,2) doesn't broadcast with (2,3)
    @test_throws DimensionMismatch z12 ∧ z23
    # (2,3) doesn't broadcast with (3,2)
    @test_throws DimensionMismatch z32 ∨ z23

    # Nested wrong sizes also aren't broadcastable
    @test_throws DimensionMismatch (z1∨z23) ∨ z32
end

@testset "Logical operations" begin
    z1 = Bool(1)
    z12 = Bool(1,2)
    z32 = Bool(3,2)
    z23 = Bool(2,3)

    # and(z) = z and or(z) = z
    @test and([z1]) == z1
    @test or([z23]) == z23
    
	# Can construct with 2 exprs
    @test all((z1 ∧ z32).children .== [z1, z32]) && (z1 ∧ z32).op == :And
    #@test  (z1 ∧ z32).name == "and_z1...z32"
    @test all((z1 ∨ z32).children .== [z1, z32]) && (z1 ∨ z32).op == :Or
    #@test  (z1 ∨ z32).name == "or_z1...z32"

    # Can construct with N>2 exprs
    or_N = or([z1, z12, z32])
    and_N = and([z1, z12, z32])

    @test all(or_N.children .== [z1, z12, z32]) 
    #@test  and_N.name == "and_z1...z32"

    @test all(or_N.children .== [z1, z12, z32]) 
	#@test  or_N.name == "or_z1...z32"
    
    # Can construct negation
    @test (¬z32).op == :Not && (¬z32).children == [z32,]
    #@test (¬z32).name == "~z32"

    # Can construct Implies
    @test (z1⟹z23) == (z23∨(¬z1))
 
end