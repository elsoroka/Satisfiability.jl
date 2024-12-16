@testitem "Int Real" begin

    using Satisfiability

    @testset "Construct Int and Real expressions" begin
        @satvariable(a, Int)
        @satvariable(b[1:2], Int)
        @satvariable(c[1:1,1:2], Int)

        @satvariable(ar, Real)
        @satvariable(br[1:2], Real)
        @satvariable(cr[1:1,1:2], Real)

        @satvariable(z, Bool)
        @test isequal(convert(IntExpr, z), ite(z, 1, 0))
        @test isequal(convert(RealExpr, z), ite(z, 1.0, 0.0))
        @test isequal(z+z, ite(z, 1, 0) + ite(z, 1, 0))

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
        @test isequal((cr .>= 0)[1,1] , cr[1,1] >= 0) && isequal((cr .<= 0.0)[1,1] , cr[1,1] <= 0.0)
        @test isequal((cr .== false)[1,1] , cr[1,1] == false)
        @test isequal((cr .< false)[1,1] , cr[1,1] < false) && isequal((cr .> 0)[1,1] , cr[1,1] > 0)


        # Construct with constants on LHS
        @test isequal((0 .>= c)[1,1] , 0 >= c[1,1]) && isequal((0.0 .<= c)[1,1] , 0.0 <= c[1,1])
        @test isequal((0 .== c)[1,1] , c[1,1] == 0)
        @test isequal((0 .< c)[1,1] , 0 < c[1,1]) && isequal((0 .> c)[1,1] , 0 > c[1,1])
        @test isequal((1 .- c)[1,1], 1 - c[1,1]) && isequal((2 .* c)[1,1], c[1,1] * 2) && isequal((2 ./ br)[1], 2 / br[1])

        # distinct
        @test isequal(distinct(c[1,2], c[1,1]), c[1,2] != c[1,1])
        @test distinct(3,4) && !distinct(true, true)
        @test isequal(distinct(b), distinct(b[2], b[1]))
        @test isequal(distinct(ar, 2), distinct(ar, 2.0))
    end

    @testset "Construct n-ary ops" begin
        @satvariable(α, Int)
        @satvariable(b[1:2], Int)
        @satvariable(αr, Real)
        @satvariable(br[1:2], Real)

        # Operations with expressions only
        @test all(isa.(α .+ b, IntExpr))
        @test all(isa.(b .- α, IntExpr))
        @test all(isa.(br .* αr, RealExpr))
        @test all(isa.(α ./ b, RealExpr))

        @test isequal(α*α*α, α^3)
        @test isequal(α^(-1), 1.0/to_real(α))
        @test isequal((1.0/αr)*(1.0/αr), αr^(-2))

        # Operations with mixed constants and type promotion
        # Adding Int and Bool types results in an IntExpr
        children = [α, IntExpr(:const, AbstractExpr[], 2, "const_2")]
        @test isequal(sum([α, 1, true]), IntExpr(:add, children, nothing, Satisfiability.__get_hash_name(:add, children, is_commutative=true)))
        
        # Type promotion to RealExpr works when we add a float-valued literal
        children = [α, RealExpr(:const, AbstractExpr[], 3., "const_3.0")]
        @test isequal(sum([1.0, α, true, 1]), RealExpr(:add, children, nothing, Satisfiability.__get_hash_name(:add, children, is_commutative=true)))

        # Type promotion to RealExpr works when we add a real-valued expr
        children = [to_real(α), to_real(b[1]), RealExpr(:const, AbstractExpr[], 2.0, "const_2.0")]
        @test isequal(sum([α, 1.0, 1, false, b[1]]), RealExpr(:add, children, nothing, Satisfiability.__get_hash_name(:add, children, is_commutative=true)))

        # Sum works automatically
        @test isequal(1 + div(α, b[1]) + mod(b[1], b[2]) + true, sum([1, div(α, b[1]), mod(b[1], b[2]), true]))

        @test all(isequal.((α - 3).children, [α, IntExpr(:const, AbstractExpr[], 3, "const_3")]))
        @test all(isequal.((αr/3.0).children, [αr, RealExpr(:const, AbstractExpr[], 3., "const_3.0")]))

        # div, /, mod type coercion
        @test isequal(div(2.0, αr), div(2, to_int(αr)))
        @test isequal(div(αr, 2.0), div(to_int(αr), 2))
        @test isequal(mod(αr, 3.0), mod(to_int(αr), 3))
        @test isequal(mod(3.0, αr), mod(3, to_int(αr)))
        @test isequal(α/2, to_real(α)/2.0)

        # abs rewrites to ite for non-int variables
        @satvariable(z, Bool)
        @test isequal(abs(z), ite(z, 1, 0))
        @test isequal(abs(αr), ite(αr >= 0.0, αr, -αr))
    end

    @testset "Assignment and conversion" begin
        @satvariable(aR, Real)
        @satvariable(a, Int)
        d = Dict("aR" => 1.0, "a"=>-1)
        e1 = aR + a <= 0 # this should promote to real
        e2 = to_int(aR) + a <= 0 # this should be int
        assign!(e1, d)
        assign!(e2, d)
        @test(isa(value(to_real(a)), Float64) && value(to_real(a)) == -1.0)
        @test(isa(value(to_int(aR)), Integer) && value(to_int(aR)) == 1)

        # Conversion to same type is an identity operation
        @test(isequal(aR, to_real(aR)))
        @test(isequal(a, to_int(a)))
    end
end
