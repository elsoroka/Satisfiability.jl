import Base.xor, Base.!

include("BoolExpr.jl")
include("utilities.jl")

##### NAMING COMBINED BOOLEXPRS #####

"Given an array of named BoolExprs, returns a combined name for use when naming exprs that have multiple children.
Example: array with names z_1_1,...,z_m_n returns string z_1_1...z_m_n if m*n>max_items. If m*n <= max_items, all names are listed."
function __get_combined_name(zs::Array{T}; is_commutative=false) where T <: AbstractExpr
    if is_commutative
        names = sort(vec(getproperty.(zs, :name)))
    else
        names = vec(getproperty.(zs, :name))
    end
    return join(names, "__")
end

function __get_hash_name(op::Symbol, zs::Array{T}; is_commutative=false) where T <: AbstractExpr
    combined_name = __get_combined_name(zs, is_commutative=is_commutative)# TODO should sort when op is commutative
    return "$(op)_$(string(hash(combined_name), base=16))"
end


# combine children for Boolean n-ary ops
function __bool_nary_op(zs::Array{T}, op::Symbol, ReturnType::Type, __is_commutative=false, __try_flatten=false) where T <: BoolExpr
    if length(zs) == 1
        return zs[1]
    end
    children, name = __combine(zs, op, __is_commutative, __try_flatten)
    if __is_commutative && length(children)>1 # clear duplicates
        children = unique(children)
        name = __get_hash_name(op, children, is_commutative=__is_commutative)
    end
    # TODO here we should compute the value
    return ReturnType(op, children, nothing, name, __is_commutative=__is_commutative)
end


##### LOGICAL OPERATIONS #####

"""
    not(z::BoolExpr)
    ¬z

Return the logical negation of `z`.
    
Note: Broacasting a unary operator requires the syntax `.¬z` which can be confusing to new Julia users. We define `¬(z::Array{BoolExpr})` for convenience.

```julia
    @satvariable(z[1:n], Bool)
    ¬z  # syntactic sugar for map(¬, z)
    .¬z # also valid
```

"""
function not(z::BoolExpr)
    # catch the special case where we have not(x == y) which should be distinct(x,y)
    if z.op == :eq && length(z.children) == 2
        value = isnothing(z.value) ? nothing : !(z.value)
        return BoolExpr(:distinct, z.children, value, __get_hash_name(:distinct, z.children, is_commutative=true), __is_commutative=true)
    else
        return BoolExpr(:not, [z], isnothing(z.value) ? nothing : !(z.value), __get_hash_name(:not, [z]))
    end
end
not(zs::Array{T}) where T <: BoolExpr  = map(not, zs)
¬(z::BoolExpr)                      = not(z)
¬(zs::Array{T}) where T <: BoolExpr   = not(zs)
!(e::BoolExpr) = not(e) # this is necessary because a != b is !(a == b) so we need ! of BoolExpr to define != for AbstractExpr

∧(z1::BoolExpr, z2::BoolExpr) = and([z1, z2])
∨(z1::BoolExpr, z2::BoolExpr) = or([z1, z2])


function and(zs::Array{T}, literals=Bool[]) where T <: BoolExpr        
    if length(literals) > 0
        if !all(literals) # if any literal is 0
            return false
        elseif length(zs) == 0 # only literals, all of them must be true
            return true
        end
    end
    
    # now the remaining are BoolExpr
    expr = __bool_nary_op(zs, :and, BoolExpr, true, true)
    values = getproperty.(expr.children, :value)
    expr.value = length(values) > 0 && !any(isnothing.(values)) ? reduce(&, values) : nothing
    return expr
end

"""
    z1 ∧ z2
    and(z1,...,zn)
    and([z1,...,zn])

Returns the logical AND of two or more variables. Use dot broadcasting for vector-valued and matrix-valued Boolean expressions.

```julia
@satvariable(z1[1:n], Bool)
@satvariable(z2[n, 1:m], Bool)
z1 .∧ z2
and.(z1, z2) # equivalent to z1 .∧ z2
```

Special cases:
* `and(z)` returns `z`.
* `and(z, false)` returns `false`.
* `and(z, true)` returns `z`.
"""
and(zs::Vararg{Union{T, Bool}}) where T <: BoolExpr = and(collect(zs))
# We need this declaration to enable the syntax and.([z1, z2,...,zn]) where z1, z2,...,zn are broadcast-compatible

# and this one is for generators
and(exprs::Base.Generator) = and(collect(exprs))

function or(zs::Array{T}, literals=Bool[]) where T <: BoolExpr 
    if length(literals) > 0
        if any(literals) # if any literal is 1
            return true
        elseif length(zs) == 0 # only literals, all of them must be false
            return false
        end
    end

    expr = __bool_nary_op(zs, :or, BoolExpr, true, true)
    values = getproperty.(expr.children, :value)
    expr.value = length(values) > 0 && !any(isnothing.(values)) ? reduce(|, values) : nothing
    return expr
end

"""
    z1 ∨ z2
    or(z1,...,zn)
    or([z1,...,zn])

Returns the logical OR of two or more variables. Use dot broadcasting for vector-valued and matrix-valued Boolean expressions.

```julia
@satvariable(z1[1:n], Bool)
@satvariable(z2[1:m, 1:n], Bool)
z1 .∨ z2
or.(z1, z2) # equivalent to z1 .∨ z2
```

Special cases:
* `or(z)` returns `z`.
* `or(z, false)` returns `z`.
* `or(z, true)` returns `true`.

**Note that ∨ (`\\vee`) is NOT the ASCII character v.**
"""
or(zs::Vararg{Union{T, Bool}}) where T <: BoolExpr = or(collect(zs))
# We need this declaration to enable the syntax or.([z1, z2,...,zn]) where z1, z2,...,z are broadcast-compatible
or(exprs::Base.Generator) = or(collect(exprs))

##### ADDITIONAL OPERATORS IN THE SMT BOOL CORE SPEC #####
"""
    xor(z1,...,zn)
    ⊻(z1,...zn)

XOR (exclusive or) is true if exactly one of z1,...,zn is true and false otherwise.
Use dot broadcasting across arrays.

Special cases:
* `xor(z)` returns `z`.
* `xor(false, z)` returns `z`.
* `xor(true, z)` returns `¬z`.
* `xor(true, true, z)` returns `false`.
"""
function xor(zs_mixed::Array{T}; broadcast_type=:Elementwise) where T
    zs, literals = __check_inputs_nary_op(zs_mixed, expr_type=BoolExpr)

    if length(literals) > 0
        if sum(literals)>1 # more than one literal is true, so xor automatically is false
            return false
        elseif sum(literals) == 1
            if length(zs) > 0 # exactly one literal is true and there are variables
                # conversion is needed because zs has type Array{AbstractExpr} when it's returned from __check_inputs_nary_op
                return and(¬convert(Array{BoolExpr}, zs)) # then all variables must be false
            else # only literals
                return true
            end
        end
        # if sum(literals) == 0 they're all false so we move on
    end

    expr = __bool_nary_op(zs, :xor, BoolExpr, true, false)
    child_values = getproperty.(zs, :value)
    expr.value = any(isnothing.(child_values)) ? nothing : xor(child_values)
    return expr
end

# We need this extra line to enable the syntax xor.([z1, z2,...,zn]) where z1, z2,...,z are broadcast-compatible
xor(zs::Vararg{Union{T, Bool}}) where T <: AbstractExpr = xor(collect(zs))
xor(exprs::Base.Generator) = xor(collect(exprs))

 # this is the const version
xor(values::Union{BitVector, Array{T}}) where T <: Bool = sum(values) == 1

"""
    z1 ⟹ z2
    implies(z1, z2)

Returns the expression z1 IMPLIES z2. Use dot broadcasting for vector-valued and matrix-valued Boolean expressions. Note: `implies(z1, z2)` is equivalent to `or(not(z1), z2)`.
"""
function implies(z1::BoolExpr, z2::BoolExpr)
    zs = BoolExpr[z1, z2]
    value = isnothing(z1.value) || isnothing(z2.value) ? nothing : implies(z1.value, z2.value)
    return BoolExpr(:implies, zs, value, __get_hash_name(:implies, zs))
end

"""
    iff(z1::BoolExpr, z2::BoolExpr)
    z1 ⟺ z2

Bidirectional implication between z1 and z2. Equivalent to `and(z1 ⟹ z2, z2 ⟹ z1)`.
"""
function iff(z1::BoolExpr, z2::BoolExpr)
    zs = BoolExpr[z1, z2]
    value = isnothing(z1.value) || isnothing(z2.value) ? nothing : iff(z1.value, z2.value)
    return BoolExpr(:iff, zs, value, __get_hash_name(:iff, zs), __is_commutative=true)
end


"""
    ite(x::BoolExpr, y::AbstractExpr, z::AbstractExpr)

If-then-else statement. When x, y, and z are Bool, equivalent to `or(x ∧ y, ¬x ∧ z)`. Note that `y` and `z` may be other expression types. For example, given the variables `BoolExpr z` and `IntExpr a`, Satisfiability.jl rewrites `z + a` as `ite(z, 1, 0) + a`.
"""
function ite(x::BoolExpr, y::T, z::T) where T <: AbstractExpr
    zs = [x, y, z]
    if isa(x, Bool) # if x is literal
        return x ? y : z
    end

    value = any(isnothing.([x.value, y.value, z.value])) ? nothing : x ? y : z
    return BoolExpr(:ite, zs, value, __get_hash_name(:ite, zs))
end


##### SUPPORT FOR OPERATIONS WITH MIXED LITERALS #####

not(z::Bool) = !z
not(zs::Array{T}) where T <: Bool = not.(zs)
not(zs::BitArray) = not.(zs)

¬(z::Bool)   = not(z)
¬(zs::Array{T})   where T <: Bool = not.(zs)
¬(zs::BitArray) = not.(zs)

# These are hard-coded but the n-ary versions and(z1,...,zn), etc. already handle mixed literals.
∧(z1::BoolExpr, z2::Bool) = z2 ? z1 : false # returns z1 if z2 == true and false if z2 == false
∧(z1::Bool, z2::BoolExpr) = z1 ? z2 : false
∧(z1::Bool, z2::Bool) = z1 & z2

∨(z1::BoolExpr, z2::Bool) = z2 ? true : z1 # return true if z2 == true and z1 if z2 == false
∨(z1::Bool, z2::BoolExpr) = z1 ? true : z2
∨(z1::Bool, z2::Bool) = z1 | z2

⊻(z1::Union{Bool, BoolExpr}, z2::Union{Bool, BoolExpr}) = xor(z1, z2)

⟹(z1::Union{BoolExpr, Bool}, z2::Union{BoolExpr, Bool}) = implies(z1, z2)
implies(z1::Bool, z2::BoolExpr) = z1 ? z2 : true # not(z1) or z2
implies(z1::BoolExpr, z2::Bool) = z2 ? true : not(z1) # not(z1) or z2
implies(z1::Bool, z2::Bool) = !z1 | z2

⟺(z1::Union{BoolExpr, Bool}, z2::Union{BoolExpr, Bool}) = iff(z1, z2)
iff(z1::BoolExpr, z2::Bool) = z2 ? z1 : ¬z1 # if z2 is true z1 must be true and if z2 is false z1 must be false
iff(z1::Bool, z2::BoolExpr) = z1 ? z2 : ¬z2
iff(z1::Bool,     z2::Bool) = z1 == z2

ite(x::Bool, y::Any, z::Any) = x ? y : z
ite(x::BoolExpr, y::Any, z::T) where T <: AbstractExpr = ite(x, __wrap_const(y), z)
ite(x::BoolExpr, y::T, z::Any) where T <: AbstractExpr = ite(x, y, __wrap_const(z))
ite(x::BoolExpr, y::T, z::T) where T <: Any = ite(x, __wrap_const(y), __wrap_const(z))

"""
    value(z::BoolExpr)
    value(z::Array{BoolExpr})

Returns the satisfying assignment of `z`, or `nothing` if no satisfying assignment is known. In the array-valued case, returns `Array{Bool}` or `Array{nothing}`.

It's possible to return an array of mixed `Bool` and `nothing`. This could occur if some variables in an array do not appear in a problem, because `sat!(problem)` will not set the values of variables that do not appear in `problem`.
"""
value(zs::Array{T}) where T <: AbstractExpr = getproperty.(zs, :value)

value(z::AbstractExpr) = z.value
