import Base.all, Base.any, Base.xor

include("BoolExpr.jl")
include("utilities.jl")

##### NAMING COMBINED BOOLEXPRS #####

"Given an array of named BoolExprs with indices, returns the name stem with no indices.
Example: array with names z_1_1,...,z_m_n returns string z"
function __get_name_stem(zs::Array{T}) where T <: AbstractExpr
    if length(size(zs)) == 1
        return zs[1].name[1:end-2] # since the name here will be name_1
    elseif length(size(zs)) == 2
        return zs[1].name[1:end-4]
    else
        error("Array of size $(size(zs)) not supported.")
    end
end

"Given an array of named BoolExprs, returns a combined name for use when naming exprs that have multiple children.
Example: array with names z_1_1,...,z_m_n returns string z_1_1...z_m_n if m*n>max_items. If m*n <= max_items, all names are listed."
function __get_combined_name(zs::Array{T}; max_items=3) where T <: AbstractExpr
    names = sort(vec(getproperty.(zs, :name)))
    if length(names) > max_items
        return "$(names[1])_to_$(names[end])"
    else
        return join(names, "__")
    end
end

function __get_hash_name(op::Symbol, zs::Array{T}) where T <: AbstractExpr
    combined_name = __get_combined_name(zs, max_items=Inf)
    return "$(op)_$(string(hash(combined_name), base=16))"
end

# new version - switch to this
function __get_combined_name(names::Array{String}; max_items=3)
    names = sort(vec(names))
    if length(names) > max_items
        return "$(names[1])_to_$(names[end])"
    else
        return join(names, "__")
    end
end

function __get_hash_name(op::Symbol, names::Array{String})
    combined_name = __get_combined_name(names, max_items=Inf)
    return "$(op)_$(string(hash(combined_name), base=16))"
end

# combine children for Boolean n-ary ops
function __bool_nary_op(zs::Array{T}, op::Symbol, ReturnType::Type, __is_commutative=false, __try_flatten=false) where T <: BoolExpr
    expr = __combine(zs, op, ReturnType, __is_commutative, __try_flatten)
    if __is_commutative && length(expr.children)>0 # clear duplicates
        expr.children = unique(expr.children)
        expr.name = __get_hash_name(expr.op, expr.children)
    end
    return expr
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
not(z::BoolExpr)                        = BoolExpr(:not, [z], isnothing(z.value) ? nothing : !(z.value), __get_hash_name(:not, [z]))
not(zs::Array{T}) where T <: BoolExpr  = map(not, zs)
¬(z::BoolExpr)                      = not(z)
¬(zs::Array{T}) where T <: BoolExpr   = not(zs)

∧(z1::BoolExpr, z2::BoolExpr) = and([z1, z2])
∨(z1::BoolExpr, z2::BoolExpr) = or([z1, z2])


function and(zs_mixed::Array{T}; broadcast_type=:Elementwise) where T
    
    zs, literals = __check_inputs_nary_op(zs_mixed, expr_type=BoolExpr)

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
and(zs::Vararg{Union{T, Bool}}; broadcast_type=:Elementwise) where T <: AbstractExpr = and(collect(zs))
# We need this declaration to enable the syntax and.([z1, z2,...,zn]) where z1, z2,...,zn are broadcast-compatible

function or(zs_mixed::Array{T}; broadcast_type=:Elementwise) where T
    zs, literals = __check_inputs_nary_op(zs_mixed, expr_type=BoolExpr)

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
or(zs::Vararg{Union{T, Bool}}; broadcast_type=:Elementwise) where T <: AbstractExpr = or(collect(zs))
# We need this declaration to enable the syntax or.([z1, z2,...,zn]) where z1, z2,...,z are broadcast-compatible

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
        elseif sum(literals) == 1 && length(zs) > 0 # exactly one literal is true and there are variables
            # conversion is needed because zs has type Array{AbstractExpr} when it's returned from __check_inputs_nary_op
            return and(¬convert(Array{BoolExpr}, zs)) # then all variables must be false
        elseif length(zs) == 0 # only literals
            return xor(literals...)
        end
    end

    expr = __bool_nary_op(zs, :xor, BoolExpr, true, false)
    child_values = getproperty.(zs, :value)
    expr.value = any(isnothing.(child_values)) ? nothing : reduce(xor, child_values)
    return expr
end

# We need this extra line to enable the syntax xor.([z1, z2,...,zn]) where z1, z2,...,z are broadcast-compatible
xor(zs::Vararg{Union{T, Bool}}; broadcast_type=:Elementwise) where T <: AbstractExpr = xor(collect(zs))

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

⟺(z1::Union{BoolExpr, Bool}, z2::Union{BoolExpr, Bool}) = iff(z1, z2)

"""
    ite(x::BoolExpr, y::BoolExpr, z::BoolExpr)

If-then-else statement. Equivalent to `or(x ∧ y, ¬x ∧ z)`.
"""
function ite(x::Union{BoolExpr, Bool}, y::Union{BoolExpr, Bool}, z::Union{BoolExpr, Bool})
    zs = [x, y, z]
    if any(isa.(zs, Bool)) # if any of these is a literal
        return or(and(x, y), and(not(x), z)) # this will simplify it correctly
    end

    value = any(isnothing.([x.value, y.value, z.value])) ? nothing : (x.value & y.value) | (!(x.value) & z.value)
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

iff(z1::BoolExpr, z2::Bool) = z2 ? z1 : ¬z1 # if z2 is true z1 must be true and if z2 is false z1 must be false
iff(z1::Bool, z2::BoolExpr) = z1 ? z2 : ¬z2
iff(z1::Bool,     z2::Bool) = z1 == z2


##### ADDITIONAL OPERATIONS #####

"""
    all([z1,...,zn])
    
Return `and(z1,...,zn)`. If `z1,...,zn` are themselves `AND` operations, `all(z)`` flattens the nested `AND`.

Examples:
* `and([and(z1, z2), and(z3, z4)]) == and(z1, z2, z3, z4)`
* `and([or(z1, z3), z3, z4]) == and(or(z1, z3), z3, z4)`
"""
all(zs::Array{T}) where T <: BoolExpr = and(zs)

"""
    any([z1,...,zn])

Return `or(z1,...,zn)`. If `z1,...,zn` are themselves `OR` operations, `any(z)`` flattens the nested `OR`.
Examples:
* `any([or(z1, z2), or(z3, z4)]) == or(z1, z2, z3, z4)`
* `any([and(z1, z3), z3, z4]) == or(and(z1, z3), z3, z4)`
"""
any(zs::Array{T}) where T <: BoolExpr = or(zs)

"""
    value(z::BoolExpr)
    value(z::Array{BoolExpr})

Returns the satisfying assignment of `z`, or `nothing` if no satisfying assignment is known. In the array-valued case, returns `Array{Bool}` or `Array{nothing}`.

It's possible to return an array of mixed `Bool` and `nothing`. This could occur if some variables in an array do not appear in a problem, because `sat!(problem)` will not set the values of variables that do not appear in `problem`.
"""
value(zs::Array{T}) where T <: AbstractExpr = getproperty.(zs, :value)

value(z::AbstractExpr) = z.value
