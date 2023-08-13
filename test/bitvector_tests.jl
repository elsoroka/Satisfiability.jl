using BooleanSatisfiability
using Test

@testset "Construct variables and exprs" begin
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
    names = [:bvadd, :bvsub, :bvmul, :bvudiv, :bvurem, :bvshl, :bvlshr, :bvsrem, :bvsmod, :bvashr, :bvnor, :bvnand, :bvxnor]
    for (op, name) in zip(ops, names)
        @test isequal(op(a,b), BitVectorExpr{UInt16}(name, [a,b], nothing, BooleanSatisfiability.__get_hash_name(name, [a,b]), 16))
    end

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
    @test a[2:4].op == :extract
    @test_throws ErrorException a[0:2]
    @test_throws ErrorException a[15:30]

    # bv2int and int2bv
    @test isequal(bv2int(a), IntExpr(:bv2int, [a], nothing, "bv2int_a"))
    @satvariable(e, Int)
    @test isequal(int2bv(e, 32), BitVectorExpr{UInt32}(:int2bv, [e], nothing, "int2bv_e", 32))
end