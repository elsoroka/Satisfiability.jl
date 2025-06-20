@testitem "Floating Point" begin

    using Satisfiability
    using Satisfiability: round_float, fp_literal

    # Constructor Tests
    @testset "Constructor" begin
        # Test for FloatingPointExpr with specific eb and sb
        fp64 = FloatingPointExpr("fp64", value=2.5, eb=11, sb=53, rounding_mode=:RNE)
        @test fp64.value == 2.5
        @test fp64.name == "fp64"
        @test fp64.eb == 11
        @test fp64.sb == 53

        @test fp64.rounding_mode == :round_nearest_ties_to_even
        fp32 = FloatingPointExpr("fp32", value=3.14, eb=8, sb=24, rounding_mode=:RNE)
        @test fp32.value == 3.14
        @test fp32.name == "fp32"
        @test fp32.eb == 8
        @test fp32.sb == 24

        @test fp32.rounding_mode == :round_nearest_ties_to_even
        fp16 = FloatingPointExpr("fp16", value=1.0, eb=5, sb=11, rounding_mode=:RNE)
        @test fp16.value == 1.0
        @test fp16.name == "fp16"
        @test fp16.eb == 5
        @test fp16.sb == 11
        @test fp16.rounding_mode == :round_nearest_ties_to_even
    end

    # Floating-point type synonyms tests (Float16, Float32, Float64, Float128)
    @testset "Floating-Point Type Synonyms" begin
        fp64 = FloatingPointExpr("fp64", value=2.5, eb=11, sb=53, rounding_mode=:RNE)
        @test fp64.value == 2.5
        @test fp64.eb == 11
        @test fp64.sb == 53
        # Float16
        fp16 = FloatingPointExpr("fp16", value=1.0, eb=5, sb=11, rounding_mode=:RNE)
        @test fp16.value == 1.0
        @test fp16.eb == 5
        @test fp16.sb == 11
        # Float32
        fp32 = FloatingPointExpr("fp32", value=3.14, eb=8, sb=24, rounding_mode=:RNE)
        @test fp32.value == 3.14
        @test fp32.eb == 8
        @test fp32.sb == 24
        # Float128
        fp128 = FloatingPointExpr("fp128", value=1.23456789, eb=15, sb=113, rounding_mode=:RNE)
        @test fp128.value == 1.23456789
        @test fp128.eb == 15
        @test fp128.sb == 113
    end

    # Arithmetic Operations
    @testset "Arithmetic Operations" begin
        fp1 = FloatingPointExpr("fp1", value=2.5, eb=11, sb=53)
        fp2 = FloatingPointExpr("fp2", value=1.5, eb=11, sb=53)

        # Addition
        fp_add = fp1 + fp2
        @test fp_add.value == 4.0
        @test fp_add.name == "add"

        # Subtraction
        fp_sub = fp1 - fp2
        @test fp_sub.value == 1.0
        @test fp_sub.name == "sub"

        # Multiplication
        fp_mul = fp1 * fp2
        @test fp_mul.value == 4.0
        @test fp_mul.name == "mul"

        # Division
        fp_div = fp1 / fp2
        @test fp_div.value ≈ 2.0
        @test fp_div.name == "div"
    end

    @testset "Special Values" begin
        fp_zero = FloatingPointExpr("zero", value=0.0, eb=11, sb=53)
        @test fp_zero.value == 0.0
        @test fp_zero.name == "zero"

        fp_nan = FloatingPointExpr("NaN", value=NaN, eb=11, sb=53)
        @test isnan(fp_nan.value)
        @test fp_nan.name == "NaN"

        fp_inf = FloatingPointExpr("positive_infinity", value=Inf, eb=11, sb=53)
        @test fp_inf.value == Inf
        @test fp_inf.name == "positive_infinity"

        fp_ninf = FloatingPointExpr("negative_infinity", value=-Inf, eb=11, sb=53)
        @test fp_ninf.value == -Inf
        @test fp_ninf.name == "negative_infinity"
    end

    @testset "Conversion Tests" begin
        int_expr = IntExpr("int1")
        real_expr = RealExpr("real1")
        # IntExpr to FloatingPointExpr
        fp_from_int = convert(FloatingPointExpr, int_expr)
        @test fp_from_int.value == 0.0
        # RealExpr to FloatingPointExpr
        fp_from_real = convert(FloatingPointExpr, real_expr)
        @test fp_from_real.value == 0.0
    end

    @testset "Rounding Tests" begin
        fp = FloatingPointExpr("fp_round", value=1.23456789, eb=11, sb=53, rounding_mode=:RTP)
        rounded_value = round_float(fp.value, fp.rounding_mode)

        @test rounded_value == ceil(1.23456789)  # Round toward positive
        fp = FloatingPointExpr("fp_round", value=1.23456789, eb=11, sb=53, rounding_mode=:RTN)
        rounded_value = round_float(fp.value, fp.rounding_mode)

        @test rounded_value == floor(1.23456789)  # Round toward negative
        fp = FloatingPointExpr("fp_round", value=1.23456789, eb=11, sb=53, rounding_mode=:RTZ)
        rounded_value = round_float(fp.value, fp.rounding_mode)
        @test rounded_value == trunc(1.23456789)  # Round toward zero
    end

    @testset "Conversion Tests" begin
        int_expr = IntExpr("int1")
        real_expr = RealExpr("real1")
        fp_from_int = convert(FloatingPointExpr, int_expr)
        @test fp_from_int.value == 0.0
        @test fp_from_int.name == "convert_from_int_int1"

        fp_from_real = convert(FloatingPointExpr, real_expr)
        @test fp_from_real.value == 0.0
        @test fp_from_real.name == "convert_from_real_real1"
    end

    @testset "Test fp_literal - Positive" begin
        fp_expr = fp_literal(false, 10, 12345, 11, 53)
        expected_value = ldexp(12345 / (1 << (53 - 1)), 10 - (1 << (11 - 1)) + 1)
        @test fp_expr.value ≈ expected_value
        @test fp_expr.eb == 11
        @test fp_expr.sb == 53
    end

    @testset "Test fp_literal - Negative" begin
        fp_expr = fp_literal(true, 10, 12345, 11, 53)
        expected_value = -ldexp(12345 / (1 << (53 - 1)), 10 - (1 << (11 - 1)) + 1)
        @test fp_expr.value ≈ expected_value
        @test fp_expr.eb == 11
        @test fp_expr.sb == 53
    end

    @testset "Test fp_literal - Zero" begin
        fp_expr = fp_literal(false, 0, 0, 11, 53)
        @test fp_expr.value == 0.0
        @test fp_expr.eb == 11
        @test fp_expr.sb == 53
    end

    @testset "Test fp_literal - Small" begin
        fp_expr = fp_literal(false, -10, 123, 11, 53)
        expected_value = ldexp(123 / (1 << (53 - 1)), -10 - (1 << (11 - 1)) + 1)
        @test fp_expr.value ≈ expected_value
        @test fp_expr.eb == 11
        @test fp_expr.sb == 53
    end
end
