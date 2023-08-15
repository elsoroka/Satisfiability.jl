using BooleanSatisfiability
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

    # unary minus
    @test (-d).op == :bvneg
    # combining ops
    ops = [+, -, *, div, urem, <<, >>, srem, smod, >>>, nor, nand, xnor]
    names = [:bvadd, :bvsub, :bvmul, :bvudiv, :bvurem, :bvshl, :bvashr, :bvsrem, :bvsmod, :bvlshr, :bvnor, :bvnand, :bvxnor]
    for (op, name) in zip(ops, names)
        @test isequal(op(a,b), BitVectorExpr{UInt16}(name, [a,b], nothing, BooleanSatisfiability.__get_hash_name(name, [a,b]), 16))
    end

    # three special cases! the native Julia bitwise ops have weird forms (&)(a,b) because they are short circuitable
    @test isequal(a & b, BitVectorExpr{UInt16}(:bvand, [a,b], nothing, BooleanSatisfiability.__get_hash_name(:bvand, [a,b]), 16))
    @test isequal(a | b, BitVectorExpr{UInt16}(:bvor, [a,b], nothing, BooleanSatisfiability.__get_hash_name(:bvor, [a,b]), 16))
    @test isequal(~a, BitVectorExpr{UInt16}(:bvnot, [a], nothing, BooleanSatisfiability.__get_hash_name(:bvnot, [a]), 16))

    # n-ary ops
    @satvariable(e, BitVector, 16)
    ops = [+, *, and, or]
    names = [:bvadd, :bvmul, :bvand, :bvor]
    ct = BooleanSatisfiability.bvconst(0x00ff, 16)
    for (op, name) in zip(ops, names)
        @test isequal(op(a,b,0x00ff,e), BitVectorExpr{UInt16}(name, [a,b,ct, e], nothing, BooleanSatisfiability.__get_hash_name(name, [a,b,ct,e]), 16))
    end
    @test isequal(xnor(a,b,0x00ff,e), BitVectorExpr{UInt16}(:bvxnor, [a,b,ct,e], nothing, BooleanSatisfiability.__get_hash_name(:bvxnor, [a,b,ct,e]), 16))

    # logical ops
    ops = [<, <=, >, >=, ==, slt, sle, sgt, sge]
    names = [:bvult, :bvule, :bvugt, :bvuge, :eq, :bvslt, :bvsle, :bvsgt, :bvsge]
    for (op, name) in zip(ops, names)
        @test isequal(op(a,b), BoolExpr(name, [a,b], nothing, BooleanSatisfiability.__get_hash_name(name, [a,b])))
    end

    # concat
    @test concat(c, d).length == 16
    @test (concat(c, d) + a).length == 16

    # indexing
    @test (a[2:4]).range == UnitRange(2,4)
    @test_throws ErrorException a[0:2]
    @test_throws ErrorException a[15:30]

    # bv2int and int2bv
    @test isequal(bv2int(a), IntExpr(:bv2int, [a], nothing, BooleanSatisfiability.__get_hash_name(:bv2int, [a.name])))
    @satvariable(e, Int)
    @test isequal(int2bv(e, 32), BitVectorExpr{UInt32}(:int2bv, [e], nothing, BooleanSatisfiability.__get_hash_name(:int2bv, [e.name]), 32))
end

@testset "Interoperability with constants" begin
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
    
    @test BooleanSatisfiability.__format_smt_const(BitVectorExpr, bvconst(0x04, 6)) == "#b000100"
    @test BooleanSatisfiability.__format_smt_const(BitVectorExpr, bvconst(255, 12)) == "#x0ff"

    @satvariable(a, BitVector, 8)
    @satvariable(b, BitVector, 8)

    @test smt(concat(a, b, a), assert=false) == "(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(define-fun concat_aaa580f0c8a73d2a () (_ BitVec 24) (concat a b a))\n"
    @test smt((a + b) << 0x2, assert=false) == "(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(define-fun bvadd_e2cecf976dd1f170 () (_ BitVec 8) (bvadd a b))
(define-fun bvshl_e76bba3dcff1a5b9 () (_ BitVec 8) (bvshl bvadd_e2cecf976dd1f170 #x02))\n"

    @test smt(0xff >= b) == "(declare-const b (_ BitVec 8))
(define-fun bvuge_5f6f17cc7a31ab62 () Bool (bvuge #xff b))
(assert bvuge_5f6f17cc7a31ab62)\n"

    @test smt(0xff == a) == "(declare-const a (_ BitVec 8))
(define-fun eq_e7731db51d241c94 () Bool (= #xff a))
(assert eq_e7731db51d241c94)\n"

end

@testset "BitVector special cases for SMT generation" begin
    @satvariable(a, BitVector, 8)
    @satvariable(b, BitVector, 8)

    @satvariable(c, Int)
    @test smt(int2bv(c, 64), assert=false) == "(declare-const c Int)
(define-fun int2bv_1a6e7a9c3b2f1483 () (_ BitVec 64) ((_ int2bv 64) (as c Int)))\n"

    @test smt(bv2int(b) < 1) == "(declare-const b (_ BitVec 8))
(define-fun bv2int_9551acae52440d48 () Int (bv2int b))
(define-fun lt_6154633d9e26b5a1 () Bool (< bv2int_9551acae52440d48 1))
(assert lt_6154633d9e26b5a1)\n"

    @test smt(a[1:8] == 0xff) == "(declare-const a (_ BitVec 8))
(define-fun extract_fa232f94411b00cd () (_ BitVec 8) ((_ extract 7 0) a))
(define-fun eq_209f324f32b93226 () Bool (= extract_fa232f94411b00cd #xff))
(assert eq_209f324f32b93226)\n"
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
    vals = BooleanSatisfiability.parse_smt_output(output)
    BooleanSatisfiability.__assign!(expr, vals)
    @test a.value == 0xff
    @test b.value == 0x00

end