@testitem "ufunc" begin

    push!(LOAD_PATH, "../src")
    using Satisfiability

    CLEAR_VARNAMES!()

    @testset "Construct ufuncs" begin
        @satvariable(a, Int)
        @uninterpreted(p, Int, Bool)
        @test smt(p(a), assert=false) ≈ "(declare-fun p(Int) Bool)
(declare-fun a () Int)
(define-fun p_a () Bool (p a))\n"
        @test smt(p(a), assert=true) ≈ "(declare-fun p(Int) Bool)
(declare-fun a () Int)
(assert (p a))\n"
        @test isa(p(a), BoolExpr)
        @test isa(p(-1), BoolExpr)

        @uninterpreted(q, Bool, Int)
        @satvariable(z, Bool)
        @test isa(q(z), IntExpr)
        @test isa(q(true), IntExpr)

        @uninterpreted(r, Real, Real)
        @satvariable(s, Real)
        @test isa(r(s), RealExpr)
        @test isa(r(1.5), RealExpr)

        # ufuncs cannot accept wrong types
        @test_throws MethodError s(z)
        @test_throws MethodError q(1.5)
        @test_throws MethodError p(true)

        @test smt(p(a), assert=false) ≈ "(declare-fun p(Int) Bool)
(declare-fun a () Int)
(define-fun p_a () Bool (p a))\n"

        # this problem is from Clark Barrett's SMT-Switch paper
        @satvariable(x, BitVector, 32)
        @satvariable(y, BitVector, 32)
        x0 = x[1:8]
        y0 = y[1:8]
        @uninterpreted(f, (BitVector, 32), (BitVector, 32))
        expr = f(x) == f(y)
        @test smt(expr) ≈ "(declare-fun f((_ BitVec 32)) (_ BitVec 32))
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (f x) (f y)))\n"

        #Parse ufunc results"
        output = "(
    (define-fun x () (_ BitVec 32)
      #x000000ff)
    (define-fun y () (_ BitVec 32)
      #x00000000)
    (define-fun f ((x!0 (_ BitVec 32))) (_ BitVec 32)
      #x00000000)
  )"
        dict = Satisfiability.parse_model(output)
        @test dict["x"] == 0x000000ff && dict["y"] == 0x00000000 && dict["f"](1) == 0

        # Can assign
        assign!(expr, dict)
        @test f(x).value == 0 && f(0xff00) == 0

        # this is the output of the problem "find a function over Bools such that f(f(x)) == x, f(x) == y, x != y.
        output = "(
(define-fun x () Bool true)
(define-fun y () Bool false)
(define-fun f ((x!0 Bool)) Bool (ite (= x!0 false) true false)
)"
        dict = Satisfiability.parse_model(output)
        @test dict["x"] != dict["y"]
        @test dict["f"](dict["x"]) == dict["y"]
        @test dict["f"](dict["f"](dict["x"])) == dict["x"]
    end
end
