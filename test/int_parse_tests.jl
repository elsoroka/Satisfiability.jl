using BooleanSatisfiability
using Test

@testset "Solving an integer-valued problem" begin
a = Int("a")
b = Int("b")
expr1 = a + b + 2
@test smt(expr1) == "(declare-const a Int)
(declare-const b Int)
(define-fun ADD_99dce5c325207b7 () Int (+ 2 a b))\n"

expr = and(expr1 <= a, b >= b + 1)
result = "(declare-const a Int)
(declare-const b Int)
(define-fun ADD_99dce5c325207b7 () Int (+ 2 a b))
(define-fun LEQ_d476c845a7be63a () Bool (<= ADD_99dce5c325207b7 a))
(define-fun ADD_f0a93f0b97da1ab2 () Int (+ 1 b))
(define-fun GEQ_d3e5e06dff9812ca () Bool (>= ADD_f0a93f0b97da1ab2 b))
(define-fun AND_20084a5e2cc43534 () Bool (and GEQ_d3e5e06dff9812ca LEQ_d476c845a7be63a))
(assert AND_20084a5e2cc43534)\n"
@test smt(expr) == result

status = sat!(expr)
@test status == :SAT
@test value(a) == 0
@test value(b) == -2

end