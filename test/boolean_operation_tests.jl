using Satisfiability
using Test

@testset "Construct variables" begin
    # Write your tests here.
    @satvariable(z1, Bool)
    @test size(z1) == 1
    
    @satvariable(z32[1:3, 1:2], Bool)
    @test isa(z32,Array{BoolExpr})
    @test size(z32) == (3,2)

    @satvariable(z23[1:2,1:3], Bool)

    # Sizes are broadcastable
    @satvariable(z12[1:1,1:2], Bool)
    @satvariable(z21[1:2,1:1], Bool)
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

    # printing works
    @satvariable(z, Bool)
    @test string(not(z)) == "not_25ec308d1df79cdc\n | z\n"
end

@testset "Print variables" begin
    @satvariable(α[1:2, 1:3], Bool)
    string_α = "BoolExpr[α_1_1\n α_1_2\n α_1_3\n; α_2_1\n α_2_2\n α_2_3\n]"
    @test string(α) == string_α
    
    @satvariable(z1, Bool)
    z1.value = true
    @test string(z1) == "z1 = true\n"
end

@testset "Logical operations" begin    
    @satvariable(z1[1:1], Bool)
    @satvariable(z12[1:1, 1:2], Bool)
    @satvariable(z32[1:3, 1:2], Bool)

    # 1 and 0 cases
    @test isequal(and([z1[1]]), z1[1])
    @test_throws ErrorException and(AbstractExpr[])
    
	# Can construct with 2 exprs
    @test Satisfiability.__is_permutation((z1 .∧ z32)[1].children, [z1[1], z32[1]] )
    @test  (z1 .∧ z32)[1].name == Satisfiability.__get_hash_name(:and, [z1[1], z32[1]], is_commutative=true)
    @test Satisfiability.__is_permutation((z1 .∨ z32)[2,1].children, [z1[1], z32[2,1]] )
    @test  (z1 .∨ z32)[1].name == Satisfiability.__get_hash_name(:or, [z1[1], z32[1]], is_commutative=true)

    # Can construct with N>2 exprs
    or_N = or.(z1, z12, z32)
    and_N = and.(z1, z12, z32)

    @test Satisfiability.__is_permutation(or_N[3,2].children, [z1[1], z12[1,2], z32[3,2]] )
    exprs = [z1[1], z12[1], z32[1]]
    @test  and_N[1].name == and(e for e in exprs).name

    @test Satisfiability.__is_permutation(or_N[1].children, [z1[1], z12[1], z32[1]] )
	@test or_N[1].name == or(e for e in exprs).name
    
    # Can construct negation
    @test isequal((not(z32))[1].children, [z32[1]])
    # negation of equality simplifies to distinct when it's a 2-op
    @satvariable(a3[1:3], Bool)
    @test isequal(¬(a3[1]==a3[2]), distinct(a3[1:2]))
    # and doesn't when it's a n>2-op
    @test isequal((¬a3[1]).op, :not)
    # this tests the generator syntax
    @test isequal(distinct(a3), distinct(a3[i] for i=1:3))

    # Can construct Implies
    @test isequal((z1 .⟹ z1)[1].children, [z1[1], z1[1]])

    # Can construct == and distinct
    @test isequal(z1[1] == true, true == z1[1])
    @test isequal(z1[1] != z12[1], z12[1] != z1[1])
    @test isequal(distinct(z12), and(distinct(z12[1,1], z12[1,2])))
 end

@testset "Additional operations" begin
    @satvariable(z, Bool)
    @satvariable(z1[1:1], Bool)
    @satvariable(z12[1:1, 1:2], Bool)

    # xor
    @test all(isequal.(xor.(z1, z12), BoolExpr[xor(z12[1,1], z1[1]) xor(z12[1,2], z1[1])]))
    # weird cases
    @test_throws ErrorException xor(AbstractExpr[])
    @test all(isequal.(xor(z1), z1))
    @test xor(true, true, z) == false
    @test xor(true, false) == true

    # n case
    @test all(isequal.(xor.(z, z1, z12), BoolExpr[xor(z, z1[1], z12[1,1]) xor(z, z1[1], z12[1,2])]))

    # iff
    @test all(isequal.(iff.(z1, z12), BoolExpr[ iff(z1[1], z12[1,1]) iff(z1[1], z12[1,2]) ]))

    # ite (if-then-else)
    @test all(isequal.( ite.(z,z1, z12), BoolExpr[ ite(z, z1[1], z12[1,1]) ite(z, z1[1], z12[1,2]) ]))

    # mixed and and or doesn't flatten
    @test isequal(and([or(z, z1[1]), and(z, true)]), and(or(z, z1[1]), z))
    @test isequal(or([and(z, z1[1]), or(z, false)]), or(and(z, z1[1]), z))
end

@testset "Operations with 1D literals and 1D exprs" begin
    @satvariable(z, Bool)

    # Can operate on all literals
    @test all([not(false), ¬(¬(true))])
    @test ∧(true, true)
    @test ∨(true, false)
    @test ⟹(false, false)

    # Can operate on mixed literals and BoolExprs
    @test isequal(and(true, z), z)
    @test z ∧ false == false
    @test true ∨ z == true
    @test isequal(or(z, false, false), z)
    @test isequal(implies(z, false), ¬z) #or(¬z, false) == ¬z
    @test isequal(true ⟹ z, z)
end

@testset "Operations with 1D literals and nxm exprs" begin
    @satvariable(z[1:2, 1:3], Bool)

    # Can operate on mixed literals and BoolExprs
    @test isequal(true .∧ z, z)
    @test and.(z, false) == [false false false; false false false]
    @test z .∨ true == [true true true; true true true]
    @test isequal(or.(z, false, false), z)
    @test isequal(implies.(z, false), ¬z) #or(¬z, false) == ¬z
    @test isequal(implies.(true, z), z)
end

@testset "Operations with nxm literals and nxm exprs" begin
    A = [true false false; false true true]
    B = [true true true; true true true]
    @satvariable(z1, Bool)
    @satvariable(z[1:2, 1:3], Bool)

    # Can operate on all literal matrices
    @test any([not(BitArray(A)); ¬(¬(A))])
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
    @satvariable(z[1:1], Bool)
    @test !any(xor.(A, A)) # all false
    @test all(isequal.(xor.(A, z), [¬z z z; z ¬z ¬z]))

    @test all(iff.(A, A))
    @test all(isequal.(iff.(A, z), [z ¬z ¬z; ¬z z z]))
    @test all(isequal.(iff.(z, A), iff.(A, z)))

    y = @satvariable(y[1:1], Bool)
    @test all(isequal.(ite.(true, z, y), z ))
    @test all(isequal.(ite.(false, true, y), y ))
end