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
    @test  (z1 .∧ z32)[1].name == __get_hash_name(:AND, [z1[1], z32[1]])
    @test all( (z1 .∨ z32)[2,1].children .== [z1[1], z32[2,1]] )
    @test  (z1 .∨ z32)[1].name == __get_hash_name(:OR, [z1[1], z32[1]])

    # Can construct with N>2 exprs
    or_N = or.(z1, z12, z32)
    and_N = and.(z1, z12, z32)

    @test all( or_N[3,2].children .== [z1[1], z12[1,2], z32[3,2]] ) 
    @test  and_N[1].name == __get_hash_name(:AND, and_N[1].children)

    @test all( or_N[1].children .== [z1[1], z12[1], z32[1]] ) 
	@test or_N[1].name == __get_hash_name(:OR, and_N[1].children)
    
    # Can construct negation
    @test (¬z32)[1].children == [z32[1]]

    # Can construct Implies
    @test all((z1 .⟹ z1) .== (z1 .∨(¬z1)))
 
    # Can construct all() and any() statements
    @test any(z1 .∨ z12) == BoolExpr(:OR,  [z1[1], z12[1,1], z12[1,2]], nothing, __get_hash_name(:OR, [z1 z12]))
    @test all(z1 .∧ z12) == BoolExpr(:AND, [z1[1], z12[1,1], z12[1,2]], nothing, __get_hash_name(:AND, [z1 z12]))
     
    # mismatched all() and any()
    @test any(z1 .∧ z12) == BoolExpr(:OR,  [z1[1] ∧ z12[1,1], z1[1] ∧ z12[1,2]], nothing, __get_hash_name(:OR, z1.∧ z12))
    @test and(z1 .∨ z12) == BoolExpr(:AND,  [z1[1] ∨ z12[1,1], z1[1] ∨ z12[1,2]], nothing, __get_hash_name(:AND, z1.∨ z12))
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
    hashname = __get_hash_name(:AND, [z1, z2[1]])
    @test smt(z1 .∧ z2) == smt(z1)*smt(z2)*"(define-fun $hashname () Bool (and z1 z2_1))\n(assert $hashname)\n"
    
    # indexing creates a 1d expression
    hashname = __get_hash_name(:AND, [z1, z12[1,2]])
    @test smt(z1 ∧ z12[1,2]) == smt(z1)*smt(z12[1,2])*"(define-fun $hashname () Bool (and z1 z12_1_2))\n(assert $hashname)\n"
    hashname = __get_hash_name(:AND, z12)
    @test smt(z12[1,1] ∧ z12[1,2]) == smt(z12[1,1])*smt(z12[1,2])*"(define-fun $hashname () Bool (and z12_1_1 z12_1_2))\n(assert $hashname)\n"
    
    # all() and any() work
    hashname = __get_hash_name(:OR, [z1 z12])
    @test smt(any(z1 .∨ z12)) == smt(z1)*smt(z12)*"(define-fun $hashname () Bool (or z1 z12_1_1 z12_1_2))\n(assert $hashname)\n"
    
    hashname = __get_hash_name(:AND, [z1 z12])
    @test smt(all(z1 .∧ z12)) == smt(z1)*smt(z12)*"(define-fun $hashname () Bool (and z1 z12_1_1 z12_1_2))\n(assert $hashname)\n"
    
    # cross all() and any() terms
    inner = z1.∨ z12
    hashname = __get_hash_name(:AND, inner)
    @test smt(all(inner)) == smt(inner)*"(define-fun $hashname () Bool (and $(inner[1].name) $(inner[2].name)))\n(assert $hashname)\n"

    inner = z1.∧ z12
    hashname = __get_hash_name(:OR, inner)
    @test smt(any(inner)) == smt(inner)*"(define-fun $hashname () Bool (or $(inner[1].name) $(inner[2].name)))\n(assert $hashname)\n"
end

@testset "Assign values" begin
    x = Bool(3, "x")
    y = Bool(2, "y")
    z = Bool("z")
    prob = and(
        all(x),
        all(x .∨ [y; z]),
        all(¬y),
        z
    )
    values = Dict{String, Bool}("x_1" => 1,"x_2" => 1,"x_3" => 0,
              "y_1" => 0, "y_2" => 0, "z" => 1,)
    BooleanSatisfiability.assign!(prob, values)
    @test value(z) == 1
    @test all(value(x) .== [1, 1 ,0])
    @test all(value(y) .== [0, 0])
end

@testset "Solving an SMT problem" begin
    x = Bool(3, "x")
    y = Bool(2, "y")
    z = Bool("z")
    exprs = [
        all(x),
        x .∨ [y; z],
        all(¬y),
        z
    ]
    status = sat!(exprs)
    @test status == :SAT
    @test value(z) == 1
    @test all(value(x) .== [1 1 1])
    @test all(value(y) .== [0 0])

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
# Fix naming to be more coherent, for example using hashing to generate unique hex names for combined operators - done 5/13/23
# Fix unittests to match new naming scheme - done

# TODO 5/16/23
# Write a function that saves the problem to a file, ending with (check-sat) - done
# Write a function that opens an smt2 input terminal to z3 and inputs the problem, then issues (check-sat) if no errors occur - modified, we made a function that calls z3 on the file
# Write a function that retrieves (parses) the solution from z3 - done
# Write larger demo with scheduling problem

# TODO 5/25/23
# Fix bugs with any() and all() - done
# Write function that propagates values from :Identity elements to logical statements
# Fix constructor to use values if they are present, eg if x.value = true then not(x).value = false
# Add support for literals
# Fix horrible bug with negation
# Fix so 1x1 expressions are single BoolExprs instead of 1x1 matrix
# Look into defining getproperty(x::Array{BoolExpr}, f::Symbol) to fix the non-working-ness of x.value
# Fix calling sat!(Array{BoolExpr}) so it works.
# Fix export to not export helper functions and use BooleanSatisfiability. to access them for unittests