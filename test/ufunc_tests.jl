push!(LOAD_PATH, "../src")
using Satisfiability
using Test

CLEAR_VARNAMES!()

@testset "Construct ufuncs" begin
    @satvariable(a, Int)
    @uninterpreted_func(p, Int, Bool)
    @test smt(p(a), assert=false) == "(declare-fun p(Int) Bool)
(declare-fun a () Int)
(define-fun p_fa232f94411b00cd () Bool (p a))\n"
    @test isa(p(a), BoolExpr)
    @test isa(p(-1), BoolExpr)

    @uninterpreted_func(q, Bool, Int)
    @satvariable(z, Bool)
    @test isa(q(z), IntExpr)
    @test isa(q(true), IntExpr)

    @uninterpreted_func(r, Real, Real)
    @satvariable(s, Real)
    @test isa(r(s), RealExpr)
    @test isa(r(1.5), RealExpr)

    # ufuncs cannot accept wrong types
    @test_throws MethodError s(z)
    @test_throws MethodError q(1.5)
    @test_throws MethodError p(true)

    @test smt(p(a), assert=false) == "(declare-fun p(Int) Bool)
(declare-fun a () Int)
(define-fun p_fa232f94411b00cd () Bool (p a))\n"

    # this problem is from Clark Barrett's SMT-Switch paper
    @satvariable(x, BitVector, 32)
    @satvariable(y, BitVector, 32)
    x0 = x[1:8]
    y0 = y[1:8]
    @uninterpreted_func(f, (BitVector, 32), (BitVector, 32))
    @test smt(f(x) == f(y)) == "(declare-fun f((_ BitVec 32)) (_ BitVec 32))
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(define-fun f_53b20e3050918288 () (_ BitVec 32) (f x))
(define-fun f_f88aef1b5c42e41f () (_ BitVec 32) (f y))
(define-fun eq_2b7ac89600c6b34c () Bool (= f_53b20e3050918288 f_f88aef1b5c42e41f))
(assert eq_2b7ac89600c6b34c)\n"
end

@testset "Parse ufunc results" begin
    output = "(
    (define-fun x () (_ BitVec 32)
      #x000000ff)
    (define-fun y () (_ BitVec 32)
      #x00000000)
    (define-fun f ((x!0 (_ BitVec 32))) (_ BitVec 32)
      #x00000000)
  )"
    dict = Satisfiability.parse_smt_output(output)
    @test dict["x"] == 0x000000ff && dict["y"] == 0x00000000 && dict["f"](1) == 0

    # this is the output of the problem "find a function over Bools such that f(f(x)) == x, f(x) == y, x != y.
    output = "(
(define-fun x () Bool true)
(define-fun y () Bool false)
(define-fun f ((x!0 Bool)) Bool (ite (= x!0 false) true false)
)"
    dict = Satisfiability.parse_smt_output(output)
    @test dict["x"] != dict["y"]
    @test dict["f"](dict["x"]) == dict["y"]
    @test dict["f"](dict["f"](dict["x"])) == dict["x"]
end