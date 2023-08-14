import Base.getindex, Base.setproperty!
import Base.+, Base.-, Base.*, Base.<<, Base.>>, Base.>>>, Base.div
import Base.>, Base.>=, Base.<, Base.<=
# >>> is arithmetic shift right, corresponding to bvashr in SMT-LIB
# >> is logical shift right, bvlshr in SMT-LIB
# << is logical shift left, bvshl in SMT-LIB
# where operators exist (or, and, not, xor)
# Base.rem and Base.% both implement the remainder in integer division.

# This design decision supports subclasses of AbstractBitVectorExpr
# which is used to represent SMT-LIB extract (indexing) of BitVectors
abstract type AbstractBitVectorExpr <: AbstractExpr end

mutable struct BitVectorExpr{T<:Integer} <: AbstractBitVectorExpr
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

mutable struct SlicedBitVectorExpr{T<:Integer} <: AbstractBitVectorExpr
    op       :: Symbol
    children :: Array{AbstractExpr}
    value    :: Union{T, Nothing, Missing}
    name     :: String
    length   :: Int
    __is_commutative :: Bool # this doesn't mean anything here and is always false
    range    :: Union{UnitRange{I}, I} where I <: Integer
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
    result = findlast((x) -> x != 0, a .>> collect(0:8*sizeof(a)))
    return !isnothing(result) ? result : 0
end

function hexstr(a::Integer)
    if sign(a) == -1
        @error("Constants must be unsigned or positive BigInts!")
    end
    return string(a, base=16, pad=sizeof(a)*2)
end


function __bvnop(op::Function, opname::Symbol, ReturnType::Type, es::Array{T}; __is_commutative=false, __try_flatten=false) where T <: AbstractBitVectorExpr
    # This expression comes about because while SMT-LIB supports any length bit vector,
    # we store the value in Julia as a standard size. So you have to mask any extra bits away.
    value = nothing
    values = getproperty.(es, :value)
    if all(.!(isnothing.(values)))
        # We are guaranteed es all have the same type by our type signature
        value = op(values...)
    end

    children, name = __combine(es, opname, __is_commutative, __try_flatten)
    if ReturnType <: AbstractBitVectorExpr
        return ReturnType{nextsize(es[1].length)}(opname, children, value, name, es[1].length, __is_commutative=__is_commutative)
    else # it must be a BoolExpr or IntExpr
        return ReturnType(opname, children, value, name)
    end
end

function __bv1op(e::AbstractBitVectorExpr, op::Function, opname::Symbol, length=nothing)
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

+(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(+, :bvadd, BitVectorExpr, [e1, e2], __is_commutative=true, __try_flatten=true)
-(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(-, :bvsub, BitVectorExpr, [e1, e2])
*(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(*, :bvmul, BitVectorExpr, [e1, e2],__is_commutative=true, __try_flatten=true)
div(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(div, :bvudiv, BitVectorExpr, [e1, e2])

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

# these all have arity 2
urem(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(rem,            :bvurem, BitVectorExpr, [e1, e2])
<<(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)  = __bvnop(<<,             :bvshl, BitVectorExpr, [e1, e2]) # shift left
>>(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)  = __bvnop(>>>,            :bvlshr, BitVectorExpr, [e1, e2]) # logical shift right

# Extra arithmetic operators supported by Z3 but not part of the SMT-LIB standard.
srem(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)     = __bvnop(__signfix(rem), :bvsrem, BitVectorExpr, [e1, e2]) # unique to z3
smod(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)     = __bvnop(__signfix(mod), :bvsmod, BitVectorExpr, [e1, e2]) # unique to z3
>>>(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(__signfix(>>),  :bvashr, BitVectorExpr, [e1, e2]) # arithmetic shift right - unique to Z3


#####    Bitwise logical operations (arity n>=2)   #####
function or(es::Array{T}, consts=Integer[]) where T <: AbstractBitVectorExpr
    if length(consts)>0
        push!(es, __wrap_bitvector_const(reduce(|, consts), es[1].length))
    end
    expr = __bvnop((a,b) -> a | b, :bvor, BitVectorExpr, es, __is_commutative=true, __try_flatten=true)
    return expr
end

or(zs::Vararg{Union{T, Integer}}) where T <: AbstractBitVectorExpr = or(collect(zs))
# We need this declaration to enable the syntax and.([z1, z2,...,zn]) where z1, z2,...,zn are broadcast-compatible

function and(es::Array{T}, consts=Integer[]) where T <: AbstractBitVectorExpr
    if length(consts)>0
        push!(es, __wrap_bitvector_const(reduce(&, consts), es[1].length))
    end
    expr = __bvnop((a,b) -> a & b, :bvand, BitVectorExpr, es, __is_commutative=true, __try_flatten=true)
    return expr
end

and(zs::Vararg{Union{T, Integer}}) where T <: AbstractBitVectorExpr = and(collect(zs))
# We need this declaration to enable the syntax and.([z1, z2,...,zn]) where z1, z2,...,zn are broadcast-compatible

∨(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = or([e1, e2])
∧(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = and([e1, e2])

# Extra logical operators supported by Z3 but not part of the SMT-LIB standard.
nor(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)    = __bvnop((a,b) -> ~(a | b), :bvnor, BitVectorExpr, [e1, e2],  __is_commutative=true)
nand(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)   = __bvnop((a,b) -> ~(a & b), :bvnand, BitVectorExpr, [e1, e2],  __is_commutative=true)

# TODO Probably all the "extra" operators should behave like this for constants
xnor(a::T,b::T) where T <: Integer = (a & b) | (~a & ~b)

function xnor(es_mixed::Array{T}) where T
    es, literals = __check_inputs_nary_op(es_mixed, const_type=Integer, expr_type=BitVectorExpr)
    if length(literals)>0
        push!(es, __wrap_bitvector_const(reduce(xnor, literals), es[1].length))
    end
    expr = __bvnop(xnor, :bvxnor, BitVectorExpr, es)
    return expr
end

xnor(zs::Vararg{Union{T, Integer}}) where T <: AbstractBitVectorExpr = xnor(collect(zs))
# We need this declaration to enable the syntax and.([z1, z2,...,zn]) where z1, z2,...,zn are broadcast-compatible

# TODO operations with arity n
# note that bvxnor is left-accumulating, so bvxnor(a, b, c) = bvxnor(bvxnor(a, b), c)
# bvnor and bvnand have arity 2

¬(e::BitVectorExpr) = __bv1op(e, ~, :bvnot)

##### Bitwise predicates #####
<(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)   = __bvnop(>,  :bvult, BoolExpr, [e1, e2])
<=(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)  = __bvnop(>=, :bvule, BoolExpr, [e1, e2])
>(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)   = __bvnop(>,  :bvugt, BoolExpr, [e1, e2])
>=(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)  = __bvnop(>=, :bvuge, BoolExpr, [e1, e2])

# Signed comparisons are supported by Z3 but not part of the SMT-LIB standard.
slt(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)      = __bvnop(__signfix(>),  :bvslt, BoolExpr, [e1, e2])
sle(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)      = __bvnop(__signfix(>=), :bvsle, BoolExpr, [e1, e2])
sgt(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)      = __bvnop(__signfix(>),  :bvsgt, BoolExpr, [e1, e2])
sge(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)      = __bvnop(__signfix(>=), :bvsge, BoolExpr, [e1, e2]) 


##### Word-level operations #####
# concat and extract are the only SMT-LIB standard operations
# z3 adds some more, note that concat can accept constants and has arity n >= 2
function concat(es::Vararg{Any})
    if !all(isa.(es, AbstractBitVectorExpr))
        @error("Only BitVectors can be concatenated!")
    end
    lengths = getproperty.(es, :length)
    length = sum(lengths)
    ReturnType = nextsize(length)

    values = getproperty.(es, :value)
    value = any(isnothing.(values)) ? nothing : concat(values, lengths, ReturnType)
    
    name = __get_hash_name(:concat, collect(getproperty.(es, :name)))
    
    return BitVectorExpr{ReturnType}(:concat, collect(es), value, name, length)
end

function concat(vals::Array{T}, bitsizes::Array{Integer}, ReturnType::Type) where T <: Integer
    value = ReturnType(0) # this generates an unsigned int or BigInt of the appropriate size
    acc = 0
    for (v, s) in zip(vals, bitsizes)
        value |= ReturnType(v) << acc
        acc += s 
    end
    return value
end


##### INDEXING #####
# SMT-LIB indexing is called extract and works in a slightly weird manner
# Here we enable indexing using the Julia slice operator.

Base.getindex(e::AbstractBitVectorExpr, ind_1::Int64, ind_2::Int64) = getindex(e, UnitRange(ind_1, ind_2))
Base.getindex(e::AbstractBitVectorExpr, ind::Int64) = getindex(e, ind, ind)

function Base.getindex(e::AbstractBitVectorExpr, ind::UnitRange{Int64})    
    if first(ind) > last(ind) || first(ind) < 1 || last(ind) > e.length
        error("Cannot extract sequence $ind from BitVector!")
    end
    
    # typeof(e).parameters[1] returns the type of the first parameter to the parametric type of e
    ReturnIntType = typeof(e).parameters[1]
    v = isnothing(e.value) ? nothing : e.value & ReturnIntType(reduce(|, map((i) -> 2^(i-1), ind)))

    # the SMT-LIB operator is (_ extract $(last(ind)) $(first(ind)))
    return SlicedBitVectorExpr{ReturnIntType}(:extract, [e], v, __get_hash_name(:extract, [e]), length(ind), false, ind) 
end


##### Translation to/from integer #####
# Be aware these have high overhead
bv2int(e::AbstractBitVectorExpr) = IntExpr(:bv2int, [e,], isnothing(e.value) ? nothing : Int(e.value), __get_hash_name(:bv2int, [e.name]))

function int2bv(e::IntExpr, size::Int)
    name = __get_hash_name(:int2bv, [e.name])
    expr = BitVectorExpr{nextsize(size)}(:int2bv, [e], isnothing(e.value) ? nothing : unsigned(e.value), name, size)
    return expr
end


##### INTEROPERABILITY WITH CONSTANTS #####
# RULE
# Given a variable with sort (_ BitVec n) and a const with sort (_ BitVec m)
# as long as m ≤ n any operation with the same size output is valid (except concat which adds them)
# Short constants will be padded with zeros because this matches Julia's behavior.

# size must be the SMT-LIB bitvector length, for example if you have a bitvector of length 12 pass in 12 NOT 16
# this function returns c of the correct Unsigned type to interoperate with the bitvector.value
# which is the smallest Unsigned type that fits the SMT-LIB bitvector length.
function __wrap_bitvector_const(c::Union{Unsigned, BigInt}, size::Int)
    minsize = bitcount(c)
    # nextsize(size) returns the correct Unsigned type
    ReturnType = nextsize(size)
    if minsize > size
        error("BitVector of size $size cannot be combined with constant of size $minsize")
    elseif minsize == size
        return BitVectorExpr{ReturnType}(:const, AbstractExpr[], c, "const_$(hexstr(c))", size)
    else # it's smaller and we need to pad it
        return BitVectorExpr{ReturnType}(:const, AbstractExpr[], ReturnType(c), "const_$(hexstr(c))", size)
    end
end

__2ops = [:+, :-, :*, :/, :<, :<=, :>, :>=, :(==), :sle, :slt, :sge, :sgt, :nand, :nor, :<<, :>>, :>>>, :srem, :urem, :smod]

for op in __2ops
    @eval $op(a::Union{Unsigned, BigInt}, b::AbstractBitVectorExpr) = $op(__wrap_bitvector_const(a, b.length), b)
    @eval $op(a::AbstractBitVectorExpr, b::Union{Unsigned, BigInt}) = $op(a, __wrap_bitvector_const(b, a.length))
end


##### CONSTANT VERSIONS (for value propagation) #####

function __trim_bits!(e::AbstractBitVectorExpr)
    mask = typemax(typeof(e.value)) >> (8*sizeof(typeof(e.value)) - e.length)
    e.value = e.value & mask
end

