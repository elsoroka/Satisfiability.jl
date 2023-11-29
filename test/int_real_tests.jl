using Satisfiability
using Test

@testset "Construct Int and Real expressions" begin
    @satvariable(a, Int)
    @satvariable(b[1:2], Int)
    @satvariable(c[1:1,1:2], Int)

    @satvariable(ar, Real)
    @satvariable(br[1:2], Real)
    @satvariable(cr[1:1,1:2], Real)

    a.value = 2; b[1].value = 1
    @test isequal((a .< b)[1], BoolExpr(:lt, AbstractExpr[a, b[1]], false, Satisfiability.__get_hash_name(:lt, [a,b[1]])))
    @test isequal((a .>= b)[1], BoolExpr(:geq, AbstractExpr[a, b[1]], true, Satisfiability.__get_hash_name(:geq, [a,b[1]])))

    ar.value = 2.1; br[1].value = 0.9
    @test isequal((ar .> br)[1], BoolExpr(:gt, AbstractExpr[ar, br[1]], true, Satisfiability.__get_hash_name(:gt, [ar,br[1]])))
    @test isequal((ar .<= br)[1], BoolExpr(:leq, AbstractExpr[ar, br[1]], false, Satisfiability.__get_hash_name(:leq, [ar,br[1]])))

    @test isequal((-c)[1,2], IntExpr(:neg, [c[1,2]], nothing, Satisfiability.__get_hash_name(:neg, [c[1,2]])))
    @test isequal((-cr)[1,2], RealExpr(:neg, [cr[1,2]], nothing, Satisfiability.__get_hash_name(:neg, [cr[1,2]])))

    # Construct with constants on RHS
    c[1,2].value = 1
    c[1,1].value = 0
    @test isequal((c .>= 0)[1,1] , c[1,1] >= 0) && isequal((c .<= 0.0)[1,1] , c[1,1] <= 0.0)
    @test isequal((c .== 0)[1,1] , c[1,1] == 0)
    @test isequal((c .< 0)[1,1] , c[1,1] < 0) && isequal((c .> 0)[1,1] , c[1,1] > 0)

    
    # Construct with constants on LHS
    @test isequal((0 .>= c)[1,1] , 0 >= c[1,1]) && isequal((0.0 .<= c)[1,1] , 0.0 <= c[1,1])
    @test isequal((0 .== c)[1,1] , c[1,1] == 0)
    @test isequal((0 .< c)[1,1] , 0 < c[1,1]) && isequal((0 .> c)[1,1] , 0 > c[1,1])
    @test isequal((1 .- c)[1,1], 1 - c[1,1]) && isequal((2 .* c)[1,1], c[1,1] * 2) && isequal((2 ./ br)[1], 2 / br[1])

    # distinct
    @test isequal(distinct(c[1,2], c[1,1]), c[1,2] != c[1,1])
    @test distinct(3,4) && !distinct(true, true)
    @test isequal(distinct(b), distinct(b[2], b[1]))
end

@testset "Construct n-ary ops" begin
    @satvariable(a, Int)
    @satvariable(b[1:2], Int)
    @satvariable(ar, Real)
    @satvariable(br[1:2], Real)

    # Operations with expressions only
    @test all(isa.(a .+ b, IntExpr))
    @test all(isa.(b .- a, IntExpr))
    @test all(isa.(br .* ar, RealExpr))
    @test all(isa.(a ./ b, RealExpr))


    # Operations with mixed constants and type promotion
    # Adding Int and Bool types results in an IntExpr
    children = [a, IntExpr(:const, AbstractExpr[], 2, "const_2")]
    @test isequal(sum([a, 1, true]), IntExpr(:add, children, nothing, Satisfiability.__get_hash_name(:add, children, is_commutative=true)))
    
    # Type promotion to RealExpr works when we add a float-valued literal
    children = [a, RealExpr(:const, AbstractExpr[], 3., "const_3.0")]
    @test isequal(sum([1.0, a, true, 1]), RealExpr(:add, children, nothing, Satisfiability.__get_hash_name(:add, children, is_commutative=true)))

    # Type promotion to RealExpr works when we add a real-valued expr
    children = [to_real(a), to_real(b[1]), RealExpr(:const, AbstractExpr[], 2.0, "const_2.0")]
    @test isequal(sum([a, 1.0, 1, false, b[1]]), RealExpr(:add, children, nothing, Satisfiability.__get_hash_name(:add, children, is_commutative=true)))

    # Sum works automatically
    @test isequal(1 + a + b[1] + true, sum([1, a, b[1], true]))

    @test all(isequal.((a - 3).children, [a, IntExpr(:const, AbstractExpr[], 3, "const_3")]))
    @test all(isequal.((ar/3.0).children, [ar, RealExpr(:const, AbstractExpr[], 3., "const_3.0")]))

    # div, /, mod type coercion
    @test isequal(div(2.0, ar), div(2, to_int(ar)))
    @test isequal(a/2, to_real(a)/2.0)
    @test isequal(mod(ar, 2.0), mod(to_int(ar), 2))

    # abs rewrites to ite for non-int variables
    @satvariable(z, Bool)
    @test isequal(abs(z), ite(z, 1, 0))
    @test isequal(abs(ar), ite(ar >= 0.0, ar, -ar))
end