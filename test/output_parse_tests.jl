using Satisfiability
using Test

@testset "Basic parser tests" begin
  parse_return_root_values = Satisfiability.parse_return_root_values
  evaluate_values = Satisfiability.evaluate_values
  split_arguments = Satisfiability.split_arguments
  # const values
  @test evaluate_values(parse_return_root_values("2.0013")[1]) == 2.0013
  @test evaluate_values(parse_return_root_values("0")[1]) == 0
  @test evaluate_values(parse_return_root_values("#x00ff")[1]) == 255
  @test evaluate_values(parse_return_root_values("#b1111")[1]) == 15
  
  # things in parentheses
  @test evaluate_values(split_arguments("- 12")) == -12
  @test abs(evaluate_values(split_arguments("/ 2.0 3.0")) - 2.0/3.0) < 1e-6
  @test abs(evaluate_values(split_arguments("/ 1.0 (- 4.0)")) + 1.0/4.0) < 1e-6
  
  # whole SMT lines
  parse_smt_statement = Satisfiability.parse_smt_statement
  @test parse_smt_statement("define-fun b () Int\n (- 2)") == ("b", Int64, -2)
  @test parse_smt_statement("define-fun geq_e1bd460e008a4d8b () Bool
  (>= (+ 1 b) b)") == ("geq_e1bd460e008a4d8b", Bool, nothing)
  @test parse_smt_statement("define-fun yR () Real (/ 2.0 3.0)") == ("yR", Float64, 2.0/3.0)
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
)"

    result = Satisfiability.parse_smt_output(output)
    @test result == Dict("b" => -2, "a" => 0)
    output = "(
      (define-fun a () Int
        0)
      (define-fun x () Int
        1)
      (define-fun xR () Real
        (/ 2.0 3.0))
      (define-fun yR () Real
        (- (/ 5.0 6.0)))
      (define-fun y () Int
        0)
)"
    result = Satisfiability.parse_smt_output(output)
    @test abs(result["xR"] - 2.0/3.) < 1e-6
    @test abs(result["yR"] + 5.0/6.) < 1e-6

    output = "((define-fun b () Real (- 2.5))
(define-fun add_99dce5c325207b7 () Real
(+ 2 a b))
(define-fun a () Real
0.0)
))"
    result = Satisfiability.parse_smt_output(output)
    @test result == Dict("b" => -2.5, "a" => 0.0)

    output = "(
      (define-fun bvule_e2cecf976dd1f170 () Bool
        (bvule a b))
      (define-fun a () (_ BitVec 16)
        #x0000)
      (define-fun b () (_ BitVec 16)
        #x0000)
    )"

    result = "(get-model)
(
  (define-fun tmp () Real
    (/ (to_real a) (to_real b)))
  (define-fun b () Int
    0)
  (define-fun a () Int
    0)
  (define-fun /0 ((x!0 Real) (x!1 Real)) Real
    0.0)
)"
    result = Satisfiability.parse_smt_output(output)
    @test result == Dict("a" => 0,  "b" => 0)

end

# Who would do this?? But it's supported anyway.
@testset "Define fully-qualified names" begin
    @satvariable(a, Int)
    b = a
    @satvariable(a, Real)
    hashname = Satisfiability.__get_hash_name(:add, [b, a], is_commutative=true)
    @test smt(b+a, assert=false) == "(declare-fun a () Int)
(declare-fun a () Real)
(define-fun $hashname () Real (+ (as a Int) (as a Real)))
"
end