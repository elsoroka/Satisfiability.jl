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

@testset "Print variables" begin
    z = Bool(2,3,"z")
    string_z = "BoolExpr[z_1_1\n z_1_2\n z_1_3\n; z_2_1\n z_2_2\n z_2_3\n]"
    @test string(z) == string_z
    
    z1 = Bool("z1")
    z1.value = true
    @test string(z1) == "z1 = true\n"
end

@testset "Logical operations" begin
    z1 = Bool(1, "z1")
    z12 = Bool(1,2, "z12")
    z32 = Bool(3,2, "z32")

    # 1 and 0 cases
    @test isequal(and([z1[1]]), z1[1])
    @test isnothing(and(AbstractExpr[]))
    
	# Can construct with 2 exprs
    @test all( isequal.((z1 .∧ z32)[1].children, [z1[1], z32[1]] ))
    @test  (z1 .∧ z32)[1].name == BooleanSatisfiability.__get_hash_name(:AND, [z1[1], z32[1]])
    @test all( isequal.((z1 .∨ z32)[2,1].children, [z1[1], z32[2,1]] ))
    @test  (z1 .∨ z32)[1].name == BooleanSatisfiability.__get_hash_name(:OR, [z1[1], z32[1]])

    # Can construct with N>2 exprs
    or_N = or.(z1, z12, z32)
    and_N = and.(z1, z12, z32)

    @test all( isequal.(or_N[3,2].children, [z1[1], z12[1,2], z32[3,2]] ))
    @test  and_N[1].name == BooleanSatisfiability.__get_hash_name(:AND, and_N[1].children)

    @test all( isequal.(or_N[1].children, [z1[1], z12[1], z32[1]] ))
	@test or_N[1].name == BooleanSatisfiability.__get_hash_name(:OR, and_N[1].children)
    
    # Can construct negation
    @test isequal((¬z32)[1].children, [z32[1]])

    # Can construct Implies
    @test isequal((z1 .⟹ z1)[1].children, [z1[1], z1[1]])
 
    # Can construct all() and any() statements
    @test isequal(any(z1), z1[1])
    @test isequal(any(z1 .∨ z12), BoolExpr(:OR,  [z1[1], z12[1,1], z12[1,2]], nothing, BooleanSatisfiability.__get_hash_name(:OR, [z1 z12])))
    @test isequal(all(z1 .∧ z12), BoolExpr(:AND, [z1[1], z12[1,1], z12[1,2]], nothing, BooleanSatisfiability.__get_hash_name(:AND, [z1 z12])))
     
    # mismatched all() and any()
    @test isequal(any(z1 .∧ z12), BoolExpr(:OR,  [z1[1] ∧ z12[1,1], z1[1] ∧ z12[1,2]], nothing, BooleanSatisfiability.__get_hash_name(:OR, z1.∧ z12)))
    @test isequal(and(z1 .∨ z12), BoolExpr(:AND,  [z1[1] ∨ z12[1,1], z1[1] ∨ z12[1,2]], nothing, BooleanSatisfiability.__get_hash_name(:AND, z1.∨ z12)))
end

@testset "Additional operations" begin
    z = Bool("z")
    z1 = Bool(1, "z1")
    z12 = Bool(1,2, "z12")

    # xor
    @test all(isequal.(xor.(z1, z12), BoolExpr[xor(z1[1], z12[1,1]) xor(z1[1], z12[1,2])]))
    # weird cases
    @test isnothing(xor(AbstractExpr[]))
    @test all(isequal.(xor(z1), z1))
    @test xor(true, true, z) == false
    @test xor(true, false) == true

    # n case
    @test all(isequal.(xor.(z, z1, z12), BoolExpr[xor(z, z1[1], z12[1,1]) xor(z, z1[1], z12[1,2])]))

    # iff
    @test all(isequal.(iff.(z1, z12), BoolExpr[ iff(z1[1], z12[1,1]) iff(z1[1], z12[1,2]) ]))

    # ite (if-then-else)
    @test all(isequal.( ite.(z,z1, z12), BoolExpr[ ite(z, z1[1], z12[1,1]) ite(z, z1[1], z12[1,2]) ]))

    # mixed all and any
    @test isequal(all([or(z, z1[1]), and(z, true)]), and(or(z, z1[1]), z))
    @test isequal(any([and(z, z1[1]), or(z, false)]), or(and(z, z1[1]), z))
end

@testset "Operations with 1D literals and 1D exprs" begin
    z = Bool("z")

    # Can operate on all literals
    @test all([not(false), ¬(¬(true))])
    @test and(true, true)
    @test or(true, false, false)
    @test implies(false, false)

    # Can operate on mixed literals and BoolExprs
    @test isequal(and(true, z), z)
    @test and(z, false) == false
    @test or(true, z) == true
    @test isequal(or(z, false, false), z)
    @test isequal(implies(z, false), ¬z) #or(¬z, false) == ¬z
    @test isequal(implies(true, z), z)
end

@testset "Operations with 1D literals and nxm exprs" begin
    z = Bool(2,3,"z")

    # Can operate on mixed literals and BoolExprs
    @test isequal(and.(true, z), z)
    @test and.(z, false) == [false false false; false false false]
    @test or.(true, z) == [true true true; true true true]
    @test isequal(or.(z, false, false), z)
    @test isequal(implies.(z, false), ¬z) #or(¬z, false) == ¬z
    @test isequal(implies.(true, z), z)
end

@testset "Operations with nxm literals and nxm exprs" begin
    A = [true false false; false true true]
    B = [true true true; true true true]
    z1 = Bool("z1")
    z = Bool(2,3,"z")

    # Can operate on all literal matrices
    @test any([not(A); ¬(¬(A))])
    @test all(or.(A, A) .== A)
    @test all(or.(false, A) .== A)
    @test all(implies.(A, B))

    # Can operate on mixed literals and BoolExprs
    @test all(isequal.(and.(B, z), z))
    @test all(isequal.(or.(¬B, z), z))
    @test all(or.(z, B, false) .== B)
    @test all(isequal.(implies.(z, ¬B), ¬z))
    @test all(isequal.(implies.(z, false), ¬z))

    @test all(isequal.(and.(A, z1), [z1 false false; false z1 z1]))
    @test all(isequal.(or.(z1, A), [true z1 z1; z1 true true]))
end

@testset "More operations with literals" begin
    A = [true false false; false true true]
    z = Bool(1, "z")
    @test !any(xor.(A, A)) # all false
    @test all(isequal.(xor.(A, z), [¬z z z; z ¬z ¬z]))

    @test all(iff.(A, A))
    @test all(isequal.(iff.(A, z), [z ¬z ¬z; ¬z z z]))
    @test all(isequal.(iff.(z, A), iff.(A, z)))

    y = Bool(1, "y")
    @test all( isequal.(ite.(z, true, false), or.(and.(z, true), and.(¬z, false)) ))
    @test all( isequal.(ite.(false, y, z), or.(and.(false, y), and.(true, z)) ))
end