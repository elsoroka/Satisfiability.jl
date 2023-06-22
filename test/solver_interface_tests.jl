using BooleanSatisfiability
using Test

# assign is used after calling the solver so it belongs here.
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
    values = Dict{String, Bool}("x_1" => 1,"x_2" => 1,"x_3" => 1,
              "y_1" => 0, "y_2" => 0, "z" => 1,)
    BooleanSatisfiability.__assign!(prob, values)
    @test value(z) == 1
    @test all(value(x) .== [1, 1 ,1])
    @test all(value(y) .== [0, 0])
    
    @test all(value(prob.children) .== 1)
    @test value(prob) == 1

    # Creating a new expression where all children have assigned values also yields assigned values
    @test all(value(x .∨ [y; z]) .== 1) 
    @test value(and(prob.children[1], prob.children[2])) == 1
end


@testset "Solving a SAT problem" begin
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

    # problem is unsatisfiable
    status = sat!(exprs..., ¬z)
    @test status == :UNSAT

    @test isnothing(value(z))
    @test all(map(isnothing, value(x)))
    @test all(map(isnothing, value(y)))
end
