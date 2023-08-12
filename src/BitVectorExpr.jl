import Base.BitVector, Base.length, Base.cat, Base.getindex
import Base.+, Base.-, Base.*, Base.<<, Base.>>, Base.>>>, Base.div
import Base.>, Base.>=, Base.<, Base.<=
# >>> is arithmetic shift right, corresponding to bvashr in SMT-LIB
# >> is logical shift right, bvlshr in SMT-LIB
# << is logical shift left, bvshl in SMT-LIB
# where operators exist (or, and, not, xor)
# Base.rem and Base.% both implement the remainder in integer division.

mutable struct BitVectorExpr{T<:Integer} <: AbstractExpr
    op       :: Symbol
    children :: Array{AbstractExpr}
    value    :: Union{T, Nothing, Missing}
    name     :: String
    length   :: Int
    __is_commutative :: Bool
    
    BitVectorExpr{T}(op::Symbol,
            children::Array{C},
            value::Union{T, Nothing, Missing},
            name::String,
            length::Int;
            __is_commutative = false) where T <: Integer where C <: AbstractExpr = new(op, children, value, name, length, __is_commutative)
end

"""
    BitVector("a", n)

    Construct a single BitVector variable with name "a" and length n. Note that unlike Bool, Int, and Real, one cannot construct an array of BitVectors.
    The length n may be any positive integer.
"""
function BitVectorExpr(name::String, length::Int)
	global GLOBAL_VARNAMES
	global WARN_DUPLICATE_NAMES
	if name ∈ GLOBAL_VARNAMES[BitVectorExpr]
        if WARN_DUPLICATE_NAMES @warn("Duplicate variable name $name of type BitVector") end
    else
        push!(GLOBAL_VARNAMES[BitVectorExpr], name)
    end
	return BitVectorExpr{nextsize(length)}(:identity, AbstractExpr[], nothing, "$name", length)
end

# Constants, to match Julia conventions, may be specified in binary, hex, or octal.
# Constants may be specified in base 10 as long as they are explicitly constructed to be of type Unsigned or BigInt.
# Examples: 0xDEADBEEF (UInt32), 0b0101 (UInt8), 0o7700 (UInt16), big"123456789012345678901234567890" (BigInt)
function __wrap_const(c::Union{Unsigned, BigInt})
    nbits = bitcount(c)
    rettype = nextsize(nbits)
    return BitVectorExpr{rettype}(:const, AbstractExpr[], rettype(c), "const_0x$(string(c, base = 16, pad=sizeof(rettype)*2))", nbits)
end
# Consts can be padded, so for example you can add 0x01 (UInt8) to (_ BitVec 16)
# Variables cannot be padded! For example, 0x0101 (Uint16) cannot be added to (_ BitVec 8).

# Note that we don't have to define == because it's defined for AbstractExpr.

function nextsize(n::Integer) :: Type # works on BigInt and UInt
    if sign(n) == -1
        @error("Constants must be unsigned or positive BigInts!")
    end
    sz = 2^Integer((round(log2(n), RoundUp, digits=0)))
    sz = max(sz, 8) # sizes smaller than 8 get 8 bits
    if sz > 128
        return BigInt
    else
        return eval(Symbol("UInt$sz")) # returns the correct size of int
    end
end

function bitcount(a::Integer) # works on BigInt and UInt
    if sign(a) == -1
        @error("Constants must be unsigned or positive BigInts!")
    end
    return findlast((x) -> x != 0, a .>> collect(0:8*sizeof(a)))
end

function hexstr(a::Integer)
    if sign(a) == -1
        @error("Constants must be unsigned or positive BigInts!")
    end
    return string(a, base=16, pad=sizeof(a)*2)
end


function __bv2op(e1::BitVectorExpr, e2::BitVectorExpr, op::Function, opname::Symbol)
    if e1.length != e2.length
        @error "BitVectors have mismatched lengths $(e1.length) and $(e2.length)."
    end
    # This expression comes about because while SMT-LIB supports any length bit vector,
    # we store the value in Julia as a standard size. So you have to mask any extra bits away.
    value = nothing
    if !isnothing(e1.value) && !isnothing(e2.value)
        valtype = typeof(e1.value)
        mask = typemax(valtype) >> (8*sizeof(valtype) - e1.length)
        value = valtype(op(e1.value, e2.value) & mask)
    end
    name = __get_hash_name(opname, [e1.name, e2.name])
    if opname in [:bvule, :bvult, :bvuge, :bvugt, :bvsle, :bvslt, :bvsgt, :bvsge]
        return BoolExpr(opname, [e1, e2], value, name)    
    else
        return BitVectorExpr{nextsize(e1.length)}(opname, [e1, e2], value, name, e1.length)
    end
end

function __bv1op(e::BitVectorExpr, op::Function, opname::Symbol, length=nothing)
    length = isnothing(length) ? e.length : length
    value = nothing
    if !isnothing(e.value)
        valtype = typeof(e.value)
        mask = typemax(valtype) >> (8*sizeof(valtype) - e.length)
        value = valtype(op(e.value) & mask)
    end
    name = __get_hash_name(opname, [e.name,])
    return BitVectorExpr{nextsize(e.length)}(opname, [e,], value, name, length)
end


#####    Integer arithmetic    #####

+(e1::BitVectorExpr, e2::BitVectorExpr) = __bv2op(e1, e2, +, :bvadd)
-(e1::BitVectorExpr, e2::BitVectorExpr) = __bv2op(e1, e2, -, :bvsub)
*(e1::BitVectorExpr, e2::BitVectorExpr) = __bv2op(e1, e2, *, :bvmul)
div(e1::BitVectorExpr, e2::BitVectorExpr) = __bv2op(e1, e2, div, :bvudiv)

# unary minus
-(e::BitVectorExpr) = __bv1op(e, -, :bvneg)

# NOTE: Julia rem(a, b) and a%b return the unsigned remainder when a and b are unsigned
# the signed arithmetic is done when a and b are signed
# We do not implement % (modulus) because it could result in confusion
# The reason is Julia naturally prints unsigned integers in hex notation
# This matches how people usually think of BitVectors. So we store values as unsigned
# and cast to signed when necessary.
# But Julia decides whether to the unsigned or signed arithmetic based on the variable type
# while SMT-LIB defines only signed modulo, bvsmod. Thus it is confusing to implement Base.% or Base.rem
# We define urem and srem for the unsigned and signed things, respectively.

# Yikes! A function that returns a function.
__signfix(f::Function) = (a, b) -> unsigned(f(signed(a), signed(b)))

urem(e1::BitVectorExpr, e2::BitVectorExpr)     = __bv2op(e1, e2, rem,            :bvurem)
<<(e1::BitVectorExpr, e2::BitVectorExpr)  = __bv2op(e1, e2, <<,             :bvshl) # shift left
>>(e1::BitVectorExpr, e2::BitVectorExpr)  = __bv2op(e1, e2, >>>,            :bvlshr) # logical shift right

# Extra arithmetic operators supported by Z3 but not part of the SMT-LIB standard.
srem(e1::BitVectorExpr, e2::BitVectorExpr)     = __bv2op(e1, e2, __signfix(rem), :bvsrem) # unique to z3
smod(e1::BitVectorExpr, e2::BitVectorExpr)     = __bv2op(e1, e2, __signfix(mod), :bvsmod) # unique to z3
>>>(e1::BitVectorExpr, e2::BitVectorExpr) = __bv2op(e1, e2, __signfix(>>),  :bvashr) # arithmetic shift right - unique to Z3


#####    Bitwise logical operations    #####
∨(e1::BitVectorExpr, e2::BitVectorExpr)        = __bv2op(e1, e2, (a,b) -> a | b,    :bvor)
∧(e1::BitVectorExpr, e2::BitVectorExpr)        = __bv2op(e1, e2, (a,b) -> a & b,    :bvand)

# Extra logical operators supported by Z3 but not part of the SMT-LIB standard.
nor(e1::BitVectorExpr, e2::BitVectorExpr)      = __bv2op(e1, e2, (a,b) -> ~(a | b), :bvnor)
nand(e1::BitVectorExpr, e2::BitVectorExpr)     = __bv2op(e1, e2, (a,b) -> ~(a & b), :bvnand)
xnor(e1::BitVectorExpr, e2::BitVectorExpr)     = __bv2op(e1, e2, (a,b) -> (a & b) | (~a & ~b), :bvxnor)
# TODO operations with arity n
# note that bvxnor is left-accumulating, so bvxnor(a, b, c) = bvxnor(bvxnor(a, b), c)
# bvnor and bvnand have arity 2

¬(e::BitVectorExpr) = __bv1op(e, ~, :bvnot)

##### Bitwise predicates #####
<(e1::BitVectorExpr, e2::BitVectorExpr)   = __bv2op(e1, e2, >,  :bvult)
<=(e1::BitVectorExpr, e2::BitVectorExpr)  = __bv2op(e1, e2, >=, :bvule)
>(e1::BitVectorExpr, e2::BitVectorExpr)   = __bv2op(e1, e2, >,  :bvugt)
>=(e1::BitVectorExpr, e2::BitVectorExpr)  = __bv2op(e1, e2, >=, :bvuge)

# Signed comparisons are supported by Z3 but not part of the SMT-LIB standard.
slt(e1::BitVectorExpr, e2::BitVectorExpr)      = __bv2op(e1, e2, __signfix(>),  :bvslt)
sle(e1::BitVectorExpr, e2::BitVectorExpr)      = __bv2op(e1, e2, __signfix(>=), :bvsle)
sgt(e1::BitVectorExpr, e2::BitVectorExpr)      = __bv2op(e1, e2, __signfix(>),  :bvsgt)
sge(e1::BitVectorExpr, e2::BitVectorExpr)      = __bv2op(e1, e2, __signfix(>=), :bvsge)


##### Word-level operations #####
# concat and extract are the only SMT-LIB standard operations
# z3 adds some more
function Base.cat(es::Vararg{T}) where T <: BitVectorExpr
    length = sum(getproperty.(es, :length))
    valtype = nextsize(length)
    if any(isnothing.(getproperty.(es, :value)))
        value = nothing
    else
        value = valtype(0) # this generates an unsigned int or BigInt of the appropriate size
        acc = 0
        for e in es
            value |= valtype(e.value) << acc
            acc += e.length
        end
    end
    name = __get_hash_name(:concat, collect(getproperty.(es, :name)))
    return BitVectorExpr{nextsize(length)}(:concat, collect(es), value, name, length)
end

Base.getindex(e::BitVectorExpr, ind::UnitRange{Int64}) = getindex(e, first(ind), last(ind))
Base.getindex(e::BitVectorExpr, ind::Int64) = getindex(e, ind, ind)

function Base.getindex(e::BitVectorExpr, ind_1::Int64, ind_2::Int64)    
    if ind_1 > ind_2 || ind_1 < 1 || ind_2 > e.length
        error("Cannot extract sequence $ind_1 to $ind_2 from BitVector!")
    end
    return __bv1op(e, identity, :extract)#Symbol("(_ extract $ind_2 $ind_1)"))
end

##### Translation to/from integer #####
# Be aware these have high overhead
bv2int(e::BitVectorExpr) = IntExpr(:bv2int, [e,], isnothing(e.value) ? nothing : Int(e.value), "bv2int_$(e.name)")
function int2bv(e::IntExpr, size::Int)
    name = "int2bv_$(e.name)"
    expr = BitVectorExpr{nextsize(size)}(:int2bv, [e], isnothing(e.value) ? nothing : unsigned(e.value), name, size)#Symbol("(_ int2bv $size)"))
    return expr
end

##### INTEROPERABILITY WITH CONSTANTS #####
# RULE
# Given a variable with sort (_ BitVec n) and a const with sort (_ BitVec m)
# as long as m ≤ n any operation with the same size output is valid
# Short constants will be padded with zeros because this matches Julia's behavior.
# eg any operation except concat