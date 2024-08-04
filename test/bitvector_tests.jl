using Satisfiability
using Test

CLEAR_VARNAMES!()

@testset "Construct BitVector variables and exprs" begin
    # a few basics
    @test nextsize(16) == UInt16
    @test nextsize(17) == UInt32
    @test nextsize(15) == UInt16
    @test bitcount(0x01) == 1
    @test bitcount(0b10010) == 5

    @satvariable(a, BitVector, 16)
    @satvariable(b, BitVector, 16)
    @satvariable(c, BitVector, 12)
    @satvariable(d, BitVector, 4)
    # can make vectors
    @satvariable(bv[1:2], BitVector, 4)
    @satvariable(cv[1:2, 1:2], BitVector, 4)

    # unary minus
    @test (-d).op == :bvneg
    # combining ops
    ops = [+, -, *, div, sdiv, urem, <<, >>, srem, smod, >>>, nor, nand, xnor]
    names = [:bvadd, :bvsub, :bvmul, :bvudiv, :bvsdiv, :bvurem, :bvshl, :bvashr, :bvsrem, :bvsmod, :bvlshr, :bvnor, :bvnand, :bvxnor]
    for (op, name) in zip(ops, names)
        @test isequal(op(a,b), BitVectorExpr{UInt16}(name, [a,b], nothing, Satisfiability.__get_hash_name(name, [a,b]), 16))
    end

    # distinct
    @satvariable(dd[1:3], BitVector, 4)
    @test isequal(distinct(dd), and(distinct(dd[1], dd[2]), distinct(dd[1], dd[3]), distinct(dd[2], dd[3])))

    # three special cases! the native Julia bitwise ops have weird forms (&)(a,b) because they are short circuitable
    @test isequal(a & b, BitVectorExpr{UInt16}(:bvand, [a,b], nothing, Satisfiability.__get_hash_name(:bvand, [a,b], is_commutative=true), 16))
    @test isequal(a | b, BitVectorExpr{UInt16}(:bvor, [a,b], nothing, Satisfiability.__get_hash_name(:bvor, [a,b], is_commutative=true), 16))
    @test isequal(~a, BitVectorExpr{UInt16}(:bvnot, [a], nothing, Satisfiability.__get_hash_name(:bvnot, [a]), 16))

    # n-ary ops
    @satvariable(e, BitVector, 16)
    ops = [+, *, and, or]
    names = [:bvadd, :bvmul, :bvand, :bvor]
    ct = Satisfiability.bvconst(0x00ff, 16)
    for (op, name) in zip(ops, names)
        @test isequal(op(a,b,0x00ff,e), BitVectorExpr{UInt16}(name, [a,b,ct, e], nothing, Satisfiability.__get_hash_name(name, [a,b,ct,e]), 16))
    end
    # works over generator
    exprs = [a,b,0x00ff,e]
    @test isequal(xnor(a,b,0x00ff,e), xnor(exprs[i] for i=1:4))

    # logical ops
    ops = [<, <=, >, >=, ==, slt, sle, sgt, sge]
    names = [:bvult, :bvule, :bvugt, :bvuge, :eq, :bvslt, :bvsle, :bvsgt, :bvsge]
    for (op, name) in zip(ops, names)
        @test isequal(op(a,b), BoolExpr(name, [a,b], nothing, Satisfiability.__get_hash_name(name, [a,b])))
    end

    # concat
    @test concat(c, d).length == 16
    @test (concat(c, d) + a).length == 16

    # indexing
    @test (a[2:4]).range == UnitRange(2,4)
    @test_throws ErrorException a[0:2]
    @test_throws ErrorException a[15:30]

    # bv2int and int2bv
    @test isequal(bv2int(a), IntExpr(:bv2int, [a], nothing, Satisfiability.__get_hash_name(:bv2int, [a])))
    @satvariable(e, Int)
    @test isequal(int2bv(e, 32), BitVectorExpr{UInt32}(:int2bv, [e], nothing, Satisfiability.__get_hash_name(:int2bv, [e]), 32))
end

@testset "Interoperability with constants" begin
    # underlying helper functions reject invalid values
    @test_throws ErrorException nextsize(-1)
    @test_throws ErrorException bitcount(-1)

    @satvariable(a, BitVector, 8)
    @satvariable(b, BitVector, 8)

    @test isequal(a + 0xff, 255 + a)
    @test isequal(b - 0x02, b - 2)
    @test_throws ErrorException b + -1 + a

    a.value = 0xff
    @test concat(bvconst(0x01, 8), bvconst(0x04, 4)).value == 0x014
    @test isequal(concat(a, 0x1).value, 0x1ff) # because 0x1 is read as one bit
    @test isequal(concat(a, bvconst(0x01, 8)).value, 0xff01)
    @test isequal(concat(a, bvconst(0x01, 6)).value, 0b11111111000001)

    @test isequal(0x1 == a, 0x01 == a)
end

@testset "Spot checks for SMT generation" begin
    
    @test Satisfiability.__format_smt_const(BitVectorExpr, bvconst(0x04, 6)) == "#b000100"
    @test Satisfiability.__format_smt_const(BitVectorExpr, bvconst(255, 12)) == "#x0ff"

    @satvariable(a, BitVector, 8)
    @satvariable(b, BitVector, 8)

    @test smt(concat(a, b, a), assert=false) ≈ "(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(define-fun concat_17d687cb15cd0d00 () (_ BitVec 24) (concat a b a))\n"
    @test smt((a + b) << 0x2, assert=false) ≈ "(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(define-fun bvshl_e76bba3dcff1a5b9 () (_ BitVec 8) (bvshl (bvadd a b) #x02))\n"

    @test smt(0xff >= b) ≈ "(declare-fun b () (_ BitVec 8))
(assert (bvuge #xff b))\n"

    @test smt(0xff == a) ≈ "(declare-fun a () (_ BitVec 8))
(assert (= #xff a))\n"

end

@testset "BitVector special cases for SMT generation" begin
    @satvariable(a, BitVector, 8)
    @satvariable(b, BitVector, 8)

    @satvariable(c, Int)
    @test smt(int2bv(c, 64), assert=false) ≈ "(declare-fun c () Int)
(define-fun int2bv_1a6e7a9c3b2f1483 () (_ BitVec 64) ((_ int2bv 64) (as c Int)))\n"

    @test smt(bv2int(b) < 1) ≈ "(declare-fun b () (_ BitVec 8))
(assert (< (bv2int b) 1))\n"

    @test smt(a[1:8] == 0xff) ≈ "(declare-fun a () (_ BitVec 8))
(assert (= ((_ extract 7 0) a) #xff))\n"

    @satvariable(x, BitVector, 8)
    @test smt(repeat(x,2) == 0xff) ≈ "(declare-fun x () (_ BitVec 8))
(assert (= (concat x x) #x00ff))\n"

    @test smt(zero_extend(x,4) == 0x0) ≈ "(declare-fun x () (_ BitVec 8))
(assert (= ((_ zero_extend 4) x) #x000))\n"
    @test smt(sign_extend(x,4) == 0x0) ≈ "(declare-fun x () (_ BitVec 8))
(assert (= ((_ sign_extend 4) x) #x000))\n"

    @test smt(rotate_left(x,2) == 0x0) ≈ "(declare-fun x () (_ BitVec 8))
(assert (= ((_ rotate_left 2) x) #x00))\n"
    @test smt(rotate_right(x,2) == 0x0) ≈ "(declare-fun x () (_ BitVec 8))
(assert (= ((_ rotate_right 2) x) #x00))\n"
end

@testset "BitVector result parsing" begin
    # this output is the result of the two prior tests, bv2int(b) < 1 and a[1:8] == 0xff
    output = "(
    (define-fun b () (_ BitVec 8)
      #x00)
    (define-fun bv2int_9551acae52440d48 () Int
      (bv2int b))
    (define-fun lt_6154633d9e26b5a1 () Bool
      (< (bv2int b) 1))
    (define-fun extract_fa232f94411b00cd () (_ BitVec 8)
      ((_ extract 7 0) a))
    (define-fun eq_b1e0ef160af6310 () Bool
      (= #xff ((_ extract 7 0) a)))
    (define-fun a () (_ BitVec 8)
      #xff)
  )"
    @satvariable(a, BitVector, 8)
    @satvariable(b, BitVector, 8)
    expr = and(a[1:8] == 0xff, bv2int(b) < 1)
    vals = Satisfiability.parse_model(output)
    Satisfiability.assign!(expr, vals)
    @test a.value == 0xff
    @test b.value == 0x00

end

@testset "Assigning values" begin
    assign! = Satisfiability.assign!
    @satvariable(a, BitVector, 8)
    @satvariable(b, BitVector, 8)
    values = Dict("a" => 0x01, "b" => 0xf0)

    expr = a | b; assign!(expr, values)
    @test expr.value == 0xf1

    expr = -a - b; assign!(expr, values)
    @test expr.value == -0xf1

    expr = div(b,a); assign!(expr, values)
    @test expr.value == 0xf0

    expr = sdiv(-b,a); assign!(expr, values)
    @test expr.value == div(-0xf0, 0x01)

    expr = repeat(a, 3); assign!(expr, values)
    @test expr.value == 0x010101

    expr = repeat(0xf0, 3)
    @test expr == 0xf0f0f0

    expr = zero_extend(a, 4); assign!(expr, values)
    @test expr.value == 0x0001
    @test_throws ErrorException zero_extend(a, -2)

    expr = sign_extend(-a, 4); assign!(expr, values)
    @test expr.value == 0xffff
    @test_throws ErrorException sign_extend(a, -2)

    expr = rotate_left(b, 4); assign!(expr, values)
    @test expr.value == 0x0f
    @test_throws ErrorException rotate_left(a, -2)

    expr = rotate_right(b, 4); assign!(expr, values)
    @test expr.value == 0x0f
    @test_throws ErrorException rotate_right(a, -2)

    expr = bvcomp(a,a); assign!(expr, values)
    @test expr.value == 0b1
    expr = bvcomp(a,b); assign!(expr, values)
    @test expr.value == 0b0
end