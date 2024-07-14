import Base.getindex, Base.setproperty!, Base.length
import Base.+, Base.-, Base.*, Base.<<, Base.>>, Base.>>>, Base.div, Base.&, Base.|, Base.~, Base.repeat
if VERSION.minor >= 0x07
    import Base.nor, Base.nand
end
import Base.>, Base.>=, Base.<, Base.<=, Base.==, Base.!=
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
            length=children[1].length;
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


# some utility functions
Base.length(e::AbstractBitVectorExpr) = e.length

"""
    nextsize(n::Integer)

Returns the smallest unsigned integer type that can store a number with n bits.
If n is larger than the largest available type (`UInt128`), returns type `BigInt`.
"""
function nextsize(n::Integer) # works on BigInt and UInt
    if sign(n) == -1
        throw(ErrorException("Constants must be unsigned or positive!"))
    end
    sz = 2^Integer((round(log2(n), RoundUp, digits=0)))
    sz = max(sz, 8) # sizes smaller than 8 get 8 bits
    if sz > 128
        return BigInt
    else
        return eval(Symbol("UInt$sz")) # returns the correct size of int
    end
end

"""
    bitcount(a::Integer)

Returns the minimum number of bits required to store the number `a`.
"""
function bitcount(a::Integer) # works on BigInt and UInt
    if a == 0
        return 1
    end
    if sign(a) == -1
        throw(ErrorException("Constants must be unsigned or positive!"))
    end
    result = findlast((x) -> x != 0, a .>> collect(0:8*sizeof(a)))
    return result
end

function hexstr(a::Integer, ReturnType::Type)
    if sign(a) == -1
        throw(ErrorException("Constants must be unsigned or positive!"))
    end
    return string(a, base=16, pad=sizeof(ReturnType)*2)
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

function __bv1op(e::AbstractBitVectorExpr, op::Function, opname::Symbol, l=nothing)
    l = isnothing(l) ? e.length : l
    value = nothing
    if !isnothing(e.value)
        valtype = typeof(e.value)
        mask = typemax(valtype) >> (8*sizeof(valtype) - e.length)
        value = valtype(op(e.value) & mask)
    end
    name = __get_hash_name(opname, [e,])
    return BitVectorExpr{nextsize(e.length)}(opname, [e,], value, name, l)
end


#####    Integer arithmetic    #####

+(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(+, :bvadd, BitVectorExpr, [e1, e2], __is_commutative=true, __try_flatten=true)
-(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(-, :bvsub, BitVectorExpr, [e1, e2])
*(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(*, :bvmul, BitVectorExpr, [e1, e2],__is_commutative=true, __try_flatten=true)

"""
    div(a::BitVectorExpr, b::BitVectorExpr)

Unsigned integer division of two BitVectors.
"""
div(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(div, :bvudiv, BitVectorExpr, [e1, e2])

"""
    sdiv(a::BitVectorExpr, b::BitVectorExpr)

Signed integer division of two BitVectors.
"""
sdiv(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(__signfix(div), :bvsdiv, BitVectorExpr, [e1, e2])

# unary minus, this is an arithmetic minus not a bit flip.
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
"""
    urem(a::BitVectorExpr, b::BitVectorExpr)

Unsigned remainder of BitVector a divided by BitVector b. 
"""
urem(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(rem,            :bvurem, BitVectorExpr, [e1, e2])

"""
    a << b

Logical left shift a << b.
"""
<<(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(<<,             :bvshl, BitVectorExpr, [e1, e2]) # shift left

"""
    a >>> b

Logical right shift a >>> b.
"""
>>>(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(>>>,            :bvlshr, BitVectorExpr, [e1, e2]) # logical shift right

# Extra arithmetic operators supported by Z3 but not part of the SMT-LIB standard.

"""
    srem(a::BitVectorExpr, b::BitVectorExpr)

Signed remainder of BitVector a divided by BitVector b.
"""
srem(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(__signfix(rem), :bvsrem, BitVectorExpr, [e1, e2]) # unique to z3

"""
    smod(a::BitVectorExpr, b::BitVectorExpr)

Signed modulus of BitVector a divided by BitVector b.
"""
smod(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(__signfix(mod), :bvsmod, BitVectorExpr, [e1, e2]) # unique to z3

"""
    a >> b

Arithmetic right shift a >> b.
"""
>>(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(__signfix(>>),  :bvashr, BitVectorExpr, [e1, e2]) # arithmetic shift right - unique to Z3


#####    Bitwise logical operations (arity n>=2)   #####
function or(es::Array{T}, consts=Integer[]) where T <: AbstractBitVectorExpr
    if length(consts)>0
        push!(es, bvconst(reduce(|, consts), es[1].length))
    end
    expr = __bvnop((a,b) -> a | b, :bvor, BitVectorExpr, es, __is_commutative=true, __try_flatten=true)
    return expr
end

or(zs::Vararg{Union{T, Integer}}) where T <: AbstractBitVectorExpr = or(collect(zs))
# We need this declaration to enable the syntax and.([z1, z2,...,zn]) where z1, z2,...,zn are broadcast-compatible

function and(es::Array{T}, consts=Integer[]) where T <: AbstractBitVectorExpr
    if length(consts)>0
        push!(es, bvconst(reduce(&, consts), es[1].length))
    end
    expr = __bvnop((a,b) -> a & b, :bvand, BitVectorExpr, es, __is_commutative=true, __try_flatten=true)
    return expr
end

and(zs::Vararg{Union{T, Integer}}) where T <: AbstractBitVectorExpr = and(collect(zs))
# We need this declaration to enable the syntax and.([z1, z2,...,zn]) where z1, z2,...,zn are broadcast-compatible


"""
    a | b
    or(a, b, c...)

Bitwise or. For n>2 variables, use the or(...) notation.
"""
(|)(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = or([e1, e2])

"""
    a & b
    and(a, b, c...)

Bitwise and. For n>2 variables, use the and(...) notation.
"""
(&)(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = and([e1, e2])

# Extra logical operators supported by Z3 but not part of the SMT-LIB standard.
"""
    nor(a, b)
    a ⊽ b

Bitwise nor.
"""
nor(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)    = __bvnop((a,b) -> ~(a | b), :bvnor, BitVectorExpr, [e1, e2],  __is_commutative=true)
⊽(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = nor(e1, e2)

"""
    nand(a, b)
    a ⊼ b

Bitwise nand.
"""
nand(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)   = __bvnop((a,b) -> ~(a & b), :bvnand, BitVectorExpr, [e1, e2],  __is_commutative=true)
⊼(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = nand(e1, e2)


# note that bvxnor is left-accumulating, so bvxnor(a, b, c) = bvxnor(bvxnor(a, b), c)
# bvnor and bvnand have arity 2
xnor(a::Integer,b::Integer) = (a & b) | (~a & ~b)

function xnor(es_mixed::Array{T}) where T
    es_mixed = collect(es_mixed)
    vars, consts = __check_inputs_nary_op(es_mixed, const_type=Integer, expr_type=BitVectorExpr)
    if isnothing(vars) || length(vars)==0
        return reduce(xnor, consts)
    end

    es = map((e) -> isa(e, Integer) ? bvconst(e, vars[1].length) : e, es_mixed)
    expr = __bvnop(xnor, :bvxnor, BitVectorExpr, es)
    return expr
end

"""
    xnor(a, b)
    xnor(a, b, c...)

Bitwise xnor. When n>2 operands are provided, xnor is left-associative (that is, `xnor(a, b, c) = reduce(xnor, [a,b,c])`.
"""
xnor(zs::Vararg{Union{T, Integer}}) where T <: AbstractBitVectorExpr = xnor(collect(zs))
# We need this declaration to enable the syntax and.([z1, z2,...,zn]) where z1, z2,...,zn are broadcast-compatible
xnor(zs::Base.Generator) = xnor(collect(zs))

"""
    ~a

Bitwise not.
"""
~(e::BitVectorExpr) = __bv1op(e, ~, :bvnot)

##### Bitwise predicates #####
<(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(>,  :bvult, BoolExpr, [e1, e2])
<=(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr) = __bvnop(>=, :bvule, BoolExpr, [e1, e2])
>(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)   = __bvnop(>,  :bvugt, BoolExpr, [e1, e2])
>=(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)  = __bvnop(>=, :bvuge, BoolExpr, [e1, e2])

(==)(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)  = __bvnop((==), :eq, BoolExpr, [e1, e2])

function distinct(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)
    value = isnothing(e1.value) || isnothing(e2.value) ? nothing : e1.value != e2.value
    name = __get_hash_name(:distinct, [e1, e2], is_commutative=true)
    return BoolExpr(:distinct, [e1, e2], value, name, __is_commutative=true)
end

# Signed comparisons are supported by Z3 but not part of the SMT-LIB standard.
""""
    slt(a::BitVectorExpr, b::BitVectorExpr)

Signed less-than. This is not the same as a < b (unsigned BitVectorExpr comparison).
"""
slt(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)      = __bvnop(__signfix(>),  :bvslt, BoolExpr, [e1, e2])

"""
    sle(a::BitVectorExpr, b::BitVectorExpr)

Signed less-than-or-equal. This is not the same as a <+ b (unsigned BitVectorExpr comparison).
"""
sle(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)      = __bvnop(__signfix(>=), :bvsle, BoolExpr, [e1, e2])

"""
    sgt(a::BitVectorExpr, b::BitVectorExpr)

Signed greater-than. This is not the same as a > b (unsigned BitVectorExpr comparison).
"""
sgt(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)      = __bvnop(__signfix(>),  :bvsgt, BoolExpr, [e1, e2])

"""
    sge(a::BitVectorExpr, b::BitVectorExpr)

Signed greater-than-or-equal. This is not the same as a >= b (unsigned BitVectorExpr comparison).
"""
sge(e1::AbstractBitVectorExpr, e2::AbstractBitVectorExpr)      = __bvnop(__signfix(>=), :bvsge, BoolExpr, [e1, e2]) 


##### Word-level operations #####
# see https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV
"""
    bvcomp(a, b)
    bvcomp(a, bvconst(a, 0xffff, 16))

Bitwise comparator: iff all bits of `a` and `b` are equal, `bvcomp(a,b) = 0b1`, otherwise `0b0`.
"""
function bvcomp(a::AbstractBitVectorExpr, b::AbstractBitVectorExpr)
    ReturnIntType = nextsize(1)
    return BitVectorExpr{ReturnIntType}(:bvcomp, [a,b], bvcomp(a.value, b.value), __get_hash_name(:bvcomp, [a,b]), true)
end

bvcomp(a::Integer, b::Integer) = a == b ? 0b1 : 0b0

"""
    concat(a, b)
    concat(a, bvconst(0xffff, 16), b, bvconst(0x01, 8), ...)
    concat(bvconst(0x01, 8), bvconst(0x02, 12)...)

Concatenate BitVectorExprs and constants of varying sizes. To guarantee a constant is the correct bit size, it should be wrapped using bvconst - otherwise its size will be inferred using `bitcount`.

concat(a,b) returns a BitVector with size a.length + b.length.

Arguments are concatenated such that the first argument to concat corresponds to the most significant bits of the resulting value. Thus:
```julia
    expr = concat(bvconst(0x01, 8), bvconst(0x02, 8), bvconst(0x03, 4))
    println(expr.length) # 20
    println(expr.value) # 0x01023
```
"""
function concat(es_mixed::Array{T}) where T <: Any
    vars, consts = __check_inputs_nary_op(es_mixed, const_type=Integer, expr_type=BitVectorExpr)
    # only consts
    if isnothing(vars) || length(vars)==0
        lengths = map(bitcount, consts)
        return __concat(consts, lengths, nextsize(sum(lengths)))
    end
    
    # preserve order of inputs
    es = map((e) -> isa(e, Integer) ? bvconst(e, bitcount(e)) : e, es_mixed)
    
    lengths = getproperty.(es, :length)
    l = sum(lengths)
    ReturnType = nextsize(l)

    values = getproperty.(es, :value)
    value = any(isnothing.(values)) ? nothing : __concat(values, lengths, ReturnType)
    
    name = __get_hash_name(:concat, es)
    
    return BitVectorExpr{ReturnType}(:concat, collect(es), value, name, l)
end

concat(es_mixed::Vararg{Any}) = concat(collect(es_mixed))

# for constant values
function concat(vals::Array{T}) where T <: Integer
    lengths = map(bitcount, vals)
    return __concat(vals, lengths, nextsize(sum(lengths)))
end
function __concat(vals::Array{T}, bitsizes::Array{R}, ReturnType::Type) where T <: Integer where R <: Integer
    value = ReturnType(0) # this generates an unsigned int or BigInt of the appropriate size
    acc = sum(bitsizes)
    for (v, s) in zip(vals, bitsizes)
        acc -= s
        value |= ReturnType(v) << acc
    end
    return value
end

"""
    repeat(a::BitVectorExpr, n)
    repeat(bvconst(0xffff, 16), n)

Repeat bitvector `a` `n` times.
"""
repeat(a::AbstractBitVectorExpr, n::Int64) = concat([a for i=1:n])
repeat(a::Integer, n::Int64) = concat([a for i=1:n])

##### INDEXING #####
# SMT-LIB indexing is called extract and works in a slightly weird manner
# Here we enable indexing using the Julia slice operator.

Base.getindex(e::AbstractBitVectorExpr, ind_1::Int64, ind_2::Int64) = getindex(e, UnitRange(ind_1, ind_2))
Base.getindex(e::AbstractBitVectorExpr, ind::Int64) = getindex(e, ind, ind)

"""
    @satvariable(a, BitVector, 8)
    a[4:8] # has length 5
    a[3]

Slice or index into a `BitVectorExpr`, returning a new `BitVectorExpr` with the appropriate length. This corresponds to the SMT-LIB operation `extract`.
"""
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


##### Extension and rotation #####
"""
    zero_extend(a::BitVectorExpr, n::Int)

Pad `BitVectorExpr` `a` with zeros. `n` specifies the number of bits and must be nonnegative.
"""
function zero_extend(e::AbstractBitVectorExpr, n::Int64)
    if n < 0
        error("n must be nonnegative for zero_extend!")
    end
    ReturnIntType = nextsize(length(e) + n)
    v = isnothing(e.value) ? nothing : zero_extend(e.value, length(e), n)
    return SlicedBitVectorExpr{ReturnIntType}(:zero_extend, [e], v, __get_hash_name(:zero_extend, [e]), length(e) + n, false, n) 
end
function zero_extend(v::T, val_len::Int64, n::Int64) where T <: Integer
    ReturnIntType = nextsize(val_len + n)
    return ReturnIntType(v)
end

"""
    sign_extend(a::BitVectorExpr, n::Int)

Pad `BitVectorExpr` `a` with 0 or 1 depending on its sign. `n` specifies the number of bits and must be nonnegative.
"""
function sign_extend(e::AbstractBitVectorExpr, n::Int64)
    if n < 0
        error("n must be nonnegative for sign_extend!")
    end
    ReturnIntType = nextsize(length(e) + n)
    v = isnothing(e.value) ? nothing : sign_extend(e.value, length(e), n)
    return SlicedBitVectorExpr{ReturnIntType}(:sign_extend, [e], v, __get_hash_name(:sign_extend, [e]), length(e) + n, false, n) 
end
function sign_extend(v::T, val_len::Int64, n::Int64) where T <: Integer
    ReturnIntType = nextsize(val_len + n)
    pad = signed(v) > 0 ? ReturnIntType(0) : (typemax(ReturnIntType) << val_len)
    return ReturnIntType(v) | pad
end

"""
    rotate_left(a::BitVectorExpr, n::Int)

Rotate `BitVectorExpr` `a` by n bits left. `n` must be nonnegative.
"""
function rotate_left(e::AbstractBitVectorExpr, n::Int64)
    if n < 0
        error("n must be nonnegative for rotate_left!")
    end
    ReturnIntType = typeof(e).parameters[1]
    v = isnothing(e.value) ? nothing : bitrotate(e.value, n) # bitrotate goes left
    return SlicedBitVectorExpr{ReturnIntType}(:rotate_left, [e], v, __get_hash_name(:rotate_left, [e]), length(e), false, n) 
end
rotate_left(v::T, n::Int64) where T <: Integer = bitrotate(v, n)

"""
    rotate_right(a::BitVectorExpr, n::Int)

Rotate `BitVectorExpr` `a` by n bits right. `n` must be nonnegative.
"""
function rotate_right(e::AbstractBitVectorExpr, n::Int64)
    if n < 0
        error("n must be nonnegative for rotate_right!")
    end
    ReturnIntType = typeof(e).parameters[1]
    v = isnothing(e.value) ? nothing : bitrotate(e.value, -n) # bitrotate goes left, so -n is a right rotation
    return SlicedBitVectorExpr{ReturnIntType}(:rotate_right, [e], v, __get_hash_name(:rotate_right, [e]), length(e), false, n) 
end
rotate_right(v::T, n::Int64) where T <: Integer = bitrotate(v, -n)


##### Translation to/from integer #####
# Be aware these have high overhead
"""
    @satvariable(b, BitVector, 8)
    a = bv2int(b)

Wrap BitVectorExpr b, representing a conversion to IntExpr. The value of the integer expression will be limited by the size of the wrapped BitVector. This operation has high overhead and may impact solver performance.
"""
bv2int(e::AbstractBitVectorExpr) = IntExpr(:bv2int, [e,], isnothing(e.value) ? nothing : Int(e.value), __get_hash_name(:bv2int, [e]))

"""
    @satvariable(a, Int)
    b = int2bv(a, 8)

Wrap IntExpr a, representing a conversion to a BitVector of specified length. This operation has high overhead and may impact solver performance.

"""
function int2bv(e::IntExpr, size::Int)
    name = __get_hash_name(:int2bv, [e])
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
"""
    bvconst(0x01, 32)
    bvconst(2, 8)

Wraps a nonnegative integer constant for interoperability with BitVectorExprs. While the correct size of a BitVector constant can usually be inferred (for example, if `a` is a BitVector of length 16, the constant in `a + 0x0f` can also be wrapped to length 16), in a few cases it cannot.

Specifically, when concatenating BitVectorExprs and constants, one should wrap the constants in `bvconst` to ensure their size matches your expectations.

`bvconst` will pad constants to the requested size, but will not truncate constants. For example, `bvconst(0xffff, 12)` yields an error because `0xffff`` requires 16 bits.

"""
function bvconst(c::Integer, size::Int)
    if c < 0
        error("Cannot combine negative integer constant $c with BitVector; use unsigned(c)")
    end

    minsize = bitcount(c)
    # nextsize(size) returns the correct Unsigned type
    ReturnType = nextsize(size)
    if minsize > size
        error("BitVector of size $size cannot be combined with constant of size $minsize")
    elseif minsize == size
        return BitVectorExpr{ReturnType}(:const, AbstractExpr[], ReturnType(c), "const_0x$(hexstr(c, ReturnType))", size)
    else # it's smaller and we need to pad it
        return BitVectorExpr{ReturnType}(:const, AbstractExpr[], ReturnType(c), "const_0x$(hexstr(c, ReturnType))", size)
    end
end
# Constants, to match Julia conventions, may be specified in binary, hex, or octal.
# Constants may be specified in base 10 as long as they are explicitly constructed to be of type Unsigned or BigInt.
# Examples: 0xDEADBEEF (UInt32), 0b0101 (UInt8), 0o7700 (UInt16), big"123456789012345678901234567890" (BigInt)
# Consts can be padded, so for example you can add 0x01 (UInt8) to (_ BitVec 16)
# Variables cannot be implicitly padded! For example, 0x0101 (Uint16) cannot be added to (_ BitVec 8). To add these, use sign_extend or zero_extend.


__2ops = [:+, :-, :*, :/, :<, :<=, :>, :>=, :(==), :!=, :sle, :slt, :sge, :sgt, :nand, :nor, :<<, :>>, :>>>, :&, :|, :~, :srem, :urem, :smod]

for op in __2ops
    @eval $op(a::Integer, b::AbstractBitVectorExpr) = $op(bvconst(a, b.length), b)
    @eval $op(a::AbstractBitVectorExpr, b::Integer) = $op(a, bvconst(b, a.length))
end

##### CONSTANT VERSIONS (for value propagation) #####

function __trim_bits!(e::AbstractBitVectorExpr)
    mask = typemax(typeof(e.value)) >> (8*sizeof(typeof(e.value)) - e.length)
    e.value = e.value & mask
end

__bitvector_const_ops = Dict(
    :bvudiv => div,
    :bvsdiv => __signfix(div), # TODO check
    :bvshl => (<<),
    :bvlshr => (>>>),
    :bvashr => __signfix(>>),
    :bvand  => (&),
    :bvor => (|),
    :bvnot => ~,
    :bvneg => -,
    :bvadd => +,
    :bvsub => -,
    :bvmul => *,
    :bvurem => rem,
    :bvsrem => __signfix(rem),
    :bvsmod => __signfix(mod),
    :bvnor => (a,b) -> ~(a & b),
    :bvnand => (a,b) -> ~(a & b),
    :bvxnor => (vals) -> reduce(xnor, vals),
    :bvult => <,
    :bvule => <=,
    :bvugt => >=,
    :bvuge => >,
    :bvslt => __signfix(<),
    :bvsle => __signfix(<=),
    :bvsgt => __signfix(>=),
    :bvsge => __signfix(>),
    :bvcomp => (a,b) -> a == b ? 0b1 : 0b0, # see https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV
    :eq => (==)
)

# We overload this function from sat.jl to specialize it
# This is for propagating the values back up in __assign! (called when a problem is sat and a satisfying assignment is found).

function __propagate_value!(z::AbstractBitVectorExpr)
    vs = getproperty.(z.children, :value)

    # special cases
    if z.op == :concat
        ls = getproperty.(z.children, :length)
        z.value = __concat(vs, ls, nextsize(z.length))

    elseif z.op == :int2bv
        z.value = nextsize(z.length)(z.children[1].value)

    elseif z.op == :extract
        ReturnIntType = typeof(z).parameters[1]
        v = z.children[1].value
        z.value = v & ReturnIntType(reduce(|, map((i) -> 2^(i-1), z.range)))

    elseif z.op in [:rotate_left, :rotate_right]
        z.value = eval(z.op)(z.children[1].value, z.range)

    elseif z.op in [:zero_extend, :sign_extend]
        z.value = eval(z.op)(z.children[1].value, length(z.children[1]), z.range)
        
    elseif z.op ∈ keys(__bitvector_const_ops)
        op = __bitvector_const_ops[z.op]
        z.value = length(vs)>1 ? op(vs...) : op(vs[1])

    else
        op = eval(z.op)
        z.value = length(vs)>1 ? op(vs...) : op(vs[1])
    end
end