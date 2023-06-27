using BooleanSatisfiability
using Test

@testset "Construct Int and Real expressions" begin
    a = Int("a")
    b = Int(2, "b")
    c = Int(1,2,"c")

    ar = Real("a")
    br = Real(2, "b")
    cr = Real(1,2,"c")
    
    a.value = 2; b[1].value = 1
    @test (a .< b)[1] == BoolExpr(:LT, AbstractExpr[a, b[1]], false, BooleanSatisfiability.__get_hash_name(:LT, [a,b[1]]))
    @test (a .>= b)[1] == BoolExpr(:GEQ, AbstractExpr[a, b[1]], true, BooleanSatisfiability.__get_hash_name(:GEQ, [a,b[1]]))

    ar.value = 2.1; br[1].value = 0.9
    @test (ar .> br)[1] == BoolExpr(:GT, AbstractExpr[ar, br[1]], true, BooleanSatisfiability.__get_hash_name(:GT, [ar,br[1]]))
    @test (ar .<= br)[1] == BoolExpr(:LEQ, AbstractExpr[ar, br[1]], false, BooleanSatisfiability.__get_hash_name(:LEQ, [ar,br[1]]))

    @test (-c)[1,2] == IntExpr(:NEG, [c[1,2]], nothing, BooleanSatisfiability.__get_hash_name(:NEG, [c[1,2]]))
    @test (-cr)[1,2] == RealExpr(:NEG, [cr[1,2]], nothing, BooleanSatisfiability.__get_hash_name(:NEG, [cr[1,2]]))
end

@testset "Construct n-ary ops" begin
    a = Int("a")
    b = Int(2, "b")
    ar = Real("a")
    br = Real(2, "b")

    # Operations with expressions only
    @test all(isa.(a .+ b, IntExpr))
    @test all(isa.(b .- a, IntExpr))
    @test all(isa.(br .* ar, RealExpr))
    @test all(isa.(a ./ b, RealExpr))


    # Operations with mixed constants
    # Adding Int and Bool types results in an IntExpr
    children = [a, IntExpr(:CONST, AbstractExpr[], 2, "const_2")]
    @test sum([a, 1, true]) == IntExpr(:ADD, children, nothing, BooleanSatisfiability.__get_hash_name(:ADD, children))
    
    # Type promotion to RealExpr works when we add a float-valued literal
    children = [a, RealExpr(:CONST, AbstractExpr[], 3, "const_3.0")]
    @test sum([1.0, a, true, 1]) == RealExpr(:ADD, children, nothing, BooleanSatisfiability.__get_hash_name(:ADD, children))

    # Type promotion to RealExpr works when we add a real-valued expr
    children = [a, b[1], IntExpr(:CONST, AbstractExpr[], 2, "const_2.0")]
    @test sum([a, 1.0, 1, false, b[1]]) == RealExpr(:ADD, children, nothing, BooleanSatisfiability.__get_hash_name(:ADD, children))

    # Sum works automatically
    @test 1 + a + b[1] + true == sum([1, a, b[1], true])
end