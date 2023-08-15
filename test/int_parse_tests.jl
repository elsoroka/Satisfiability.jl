using BooleanSatisfiability
using Test

@testset "Solving an integer-valued problem" begin
CLEAR_VARNAMES!()
@satvariable(a, Int)
@satvariable(b, Int)
expr1 = a + b + 2
@test smt(expr1, assert=false) == "(declare-const a Int)
(declare-const b Int)
(define-fun add_99dce5c325207b7 () Int (+ 2 a b))\n"

expr = and(expr1 <= a, b + 1 >= b)
result = "(declare-const b Int)
(declare-const a Int)
(define-fun add_f0a93f0b97da1ab2 () Int (+ 1 b))
(define-fun geq_e1bd460e008a4d8b () Bool (>= add_f0a93f0b97da1ab2 b))
(define-fun add_99dce5c325207b7 () Int (+ 2 a b))
(define-fun leq_8df5432ee845c9e8 () Bool (<= add_99dce5c325207b7 a))
(define-fun and_8014e2e143374eea () Bool (and geq_e1bd460e008a4d8b leq_8df5432ee845c9e8))
(assert and_8014e2e143374eea)\n"
@test smt(expr) == result

status = sat!(expr)
@test status == :SAT
@test value(a) == 0
@test value(b) == -2

end

@testset "Parse some z3 output with ints and floats" begin
    output = "(
(define-fun b () Int
  (- 2))
(define-fun a () Int
  0)
(define-fun geq_e1bd460e008a4d8b () Bool
  (>= (+ 1 b) b))
(define-fun and_8014e2e143374eea () Bool
  (and (>= (+ 1 b) b) (<= (+ 2 a b) a)))
(define-fun add_99dce5c325207b7 () Int
  (+ 2 a b))
(define-fun add_f0a93f0b97da1ab2 () Int
  (+ 1 b))
(define-fun leq_8df5432ee845c9e8 () Bool
  (<= (+ 2 a b) a))
)
    "
    result = BooleanSatisfiability.parse_smt_output(output)
    @test result == Dict("b" => -2, "a" => 0)

    output = "((define-fun b () Real (- 2.5))
(define-fun add_99dce5c325207b7 () Real
(+ 2 a b))
(define-fun a () Real
0.0)
))"
    result = BooleanSatisfiability.parse_smt_output(output)
    @test result == Dict("b" => -2.5, "a" => 0.0)
end

# Who would do this?? But it's supported anyway.
@testset "Define fully-qualified names" begin
    @satvariable(a, Int)
    b = a
    @satvariable(a, Real)
    hashname = BooleanSatisfiability.__get_hash_name(:add, [b, a])
    @test smt(b+a, assert=false) == "(declare-const a Int)
(declare-const a Real)
(define-fun $hashname () Real (+ (as a Int) (as a Real)))
"
end