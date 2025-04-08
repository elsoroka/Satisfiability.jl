import Base.<, Base.<=, Base.>, Base.<=, Base.+, Base.-, Base.*, Base./, Base.^, Base.div, Base.inv, Base.mod, Base.abs, Base.==, Base.!=, Base.promote_rule, Base.convert

abstract type NumericExpr <: AbstractExpr end


mutable struct IntExpr <: NumericExpr
    op::Symbol
    children::Array{AbstractExpr}
    value::Union{Int,Bool,Nothing,Missing}
    name::String
    __is_commutative::Bool

    # for convenience
    IntExpr(op::Symbol,
        children::Array{T},
        value::Union{Int,Bool,Nothing,Missing},
        name::String;
        __is_commutative=false) where {T<:AbstractExpr} = new(op, children, value, name, __is_commutative)
end


"""
IntExpr("a")

Construct a single IntExpr variable with name "a".
"""
function IntExpr(name::String)::IntExpr
    # This unsightly bit enables warning when users define two variables with the same string name.
    global GLOBAL_VARNAMES
    global WARN_DUPLICATE_NAMES
    if name ∈ GLOBAL_VARNAMES[IntExpr]
        if WARN_DUPLICATE_NAMES
            @warn("Duplicate variable name $name of type Int")
        end
    else
        push!(GLOBAL_VARNAMES[IntExpr], name)
    end
    return IntExpr(:identity, AbstractExpr[], nothing, "$(name)")
end


mutable struct RealExpr <: NumericExpr
    op::Symbol
    children::Array{AbstractExpr}
    value::Union{Float64,Nothing,Missing}
    name::String
    __is_commutative::Bool

    # for convenience
    RealExpr(op::Symbol,
        children::Array{T},
        value::Union{Float64,Nothing,Missing},
        name::String;
        __is_commutative=false) where {T<:AbstractExpr} = new(op, children, value, name, __is_commutative)
end

"""
RealExpr("r")

Construct a single Real variable with name "r".
"""
function RealExpr(name::String)::RealExpr
    # This unsightly bit enables warning when users define two variables with the same string name.
    global GLOBAL_VARNAMES
    global WARN_DUPLICATE_NAMES
    if name ∈ GLOBAL_VARNAMES[RealExpr]
        if WARN_DUPLICATE_NAMES
            @warn("Duplicate variable name $name of type Real")
        end
    else
        push!(GLOBAL_VARNAMES[RealExpr], name)
    end
    return RealExpr(:identity, AbstractExpr[], nothing, "$(name)")
end


# These are necessary for defining interoperability between IntExpr, RealExpr, and built-in types such as Int, Bool, and Float.
NumericInteroperableExpr = Union{NumericExpr,BoolExpr}
NumericInteroperableConst = Union{Bool,Int,Float64}

__wrap_const(c::Float64) = RealExpr(:const, AbstractExpr[], c, c >= 0 ? "const_$c" : "const_neg_$(abs(c))")
__wrap_const(c::Int) = IntExpr(:const, AbstractExpr[], c, c >= 0 ? "const_$c" : "const_neg_$(abs(c))") # prevents names like -1 from being generated, which are disallowed in SMT-LIB
__wrap_const(c::Bool) = BoolExpr(:const, AbstractExpr[], c, "const_$c")


##### COMPARISON OPERATIONS ####
# These return Boolean values, eg they have sort Bool
# See figure 3.3 in the SMT-LIB standard.
"""
    a < b
    a < 0

Returns the Boolean expression a < b. Use dot broadcasting for vector-valued and matrix-valued expressions.

```julia
@satvariable(a[1:n], Int)
@satvariable(b[1:n, 1:m], Int)
a .< b
@satvariable(z, Bool)
a .< z
```
"""
function Base.:<(e1::T, e2::T) where {T<:NumericInteroperableExpr}
    value = isnothing(e1.value) || isnothing(e2.value) ? nothing : e1.value < e2.value
    name = __get_hash_name(:lt, [e1, e2])
    return BoolExpr(:lt, [e1, e2], value, name)
end

"""
    a <= b
    a <= 0

Returns the Boolean expression a <= b. Use dot broadcasting for vector-valued and matrix-valued expressions.

```julia
@satvariable(a[1:n], Int)
@satvariable(b[1:n, 1:m], Int)
a .<= b
@satvariable(z, Bool)
a .<= z
```
"""
function Base.:<=(e1::T, e2::T) where {T<:NumericInteroperableExpr}
    value = isnothing(e1.value) || isnothing(e2.value) ? nothing : e1.value <= e2.value
    name = __get_hash_name(:leq, [e1, e2])
    return BoolExpr(:leq, [e1, e2], value, name)
end

"""
    a >= b
    a >= 0

Returns the Boolean expression a >= b. Use dot broadcasting for vector-valued and matrix-valued expressions.

```julia
@satvariable(a[1:n], Int)
@satvariable(b[1:n, 1:m], Int)
a .>= b
@satvariable(z, Bool)
a .>= z
```
"""
function Base.:>=(e1::T, e2::T) where {T<:NumericInteroperableExpr}
    value = isnothing(e1.value) || isnothing(e2.value) ? nothing : e1.value >= e2.value
    name = __get_hash_name(:geq, [e1, e2])
    return BoolExpr(:geq, [e1, e2], value, name)
end

"""
    a > b
    a > 0

Returns the Boolean expression a > b. Use dot broadcasting for vector-valued and matrix-valued expressions.

```julia
@satvariable(a[1:n], Int)
@satvariable(b[1:n, 1:m], Int)
a .> b
@satvariable(z, Bool)
a .> z
```
"""
function Base.:>(e1::T, e2::T) where {T<:NumericInteroperableExpr}
    value = isnothing(e1.value) || isnothing(e2.value) ? nothing : e1.value > e2.value
    name = __get_hash_name(:gt, [e1, e2])
    return BoolExpr(:gt, [e1, e2], value, name)
end

# IMPORTANT NOTE
# THE FUNCTION (==) GENERATES AN EQUALITY CONSTRAINT
# eq() compares two AbstractExprs. and (==) because that breaks Base behavior.
# For example, if (==) generates an equality constraint instead of making a Boolean, you can't write z ∈ [z1,...,zn].

"""
    a  == b
    a == 1.0

Returns the Boolean expression a == b (arithmetic equivalence). Use dot broadcasting for vector-valued and matrix-valued expressions.

```julia
@satvariable(a[1:n], Int)
@satvariable(b[1:n, 1:m], Int)
a .== b
```

**Note:** To test whether two `AbstractExpr`s are eqivalent (in the sense that all properties are equal, not in the shared-memory-location sense of `===`), use `isequal`.
"""
function Base.:(==)(e1::T, e2::T) where {T<:NumericInteroperableExpr}
    value = isnothing(e1.value) || isnothing(e2.value) ? nothing : e1.value == e2.value
    name = __get_hash_name(:eq, [e1, e2], is_commutative=true)
    return BoolExpr(:eq, [e1, e2], value, name, __is_commutative=true)
end

"""
    distinct(x, y)
    distinct(zs::Array{AbstractExpr})

Returns the SMT-LIB `distinct` operator. `distinct(x, y)` is semantically equal to `x != y` or `not(x == y)`.
The syntax `distinct(exprs)` where `exprs` is an array of expressions is shorthand for "every element of zs is unique". Thus,
    
```julia
@satvariable(a[1:3], Int)
# this statement is true
isequal(
    distinct(a)
    and(distinct(a[1], a[2]), distinct(a[1], a[3]), distinct(a[2], a[3]))
    )
````
"""
function distinct(e1::T, e2::T) where {T<:NumericInteroperableExpr}
    value = isnothing(e1.value) || isnothing(e2.value) ? nothing : e1.value != e2.value
    name = __get_hash_name(:distinct, [e1, e2], is_commutative=true)
    return BoolExpr(:distinct, [e1, e2], value, name, __is_commutative=true)
end

# This is defined for AbstractExpr such that other types (BitVector etc) don't have to reimplement it as long as they implement the two-argument distinct
function distinct(es::Array{T}) where {T<:AbstractExpr}
    es = flatten(es) # now it's 1D
    # this expression uses Iterators.product and takes the upper triangular part of the product to avoid duplicates like (i,j) and (j,i)
    return and([distinct(es[i], es[j]) for (i, j) in Iterators.product(1:length(es), 1:length(es)) if i != j && i <= j])
end

distinct(es::Base.Generator) = distinct(collect(es))


# INTEROPERABILITY FOR COMPARISON OPERATIONS
Base.:>(e1::NumericInteroperableExpr, e2::NumericInteroperableExpr) = Base.:>(promote(e1, e2)...)
Base.:>(e1::NumericInteroperableExpr, e2::NumericInteroperableConst) = e1 > __wrap_const(e2)
Base.:>(e1::NumericInteroperableConst, e2::NumericInteroperableExpr) = __wrap_const(e1) > e2

Base.:>=(e1::NumericInteroperableExpr, e2::NumericInteroperableExpr) = Base.:>=(promote(e1, e2)...)
Base.:>=(e1::NumericInteroperableExpr, e2::NumericInteroperableConst) = e1 >= __wrap_const(e2)
Base.:>=(e1::NumericInteroperableConst, e2::NumericInteroperableExpr) = __wrap_const(e1) >= e2

Base.:<(e1::NumericInteroperableExpr, e2::NumericInteroperableExpr) = Base.:<(promote(e1, e2)...)
Base.:<(e1::NumericInteroperableExpr, e2::NumericInteroperableConst) = e1 < __wrap_const(e2)
Base.:<(e1::NumericInteroperableConst, e2::NumericInteroperableExpr) = __wrap_const(e1) < e2

Base.:<=(e1::NumericInteroperableExpr, e2::NumericInteroperableExpr) = Base.:<=(promote(e1, e2)...)
Base.:<=(e1::NumericInteroperableExpr, e2::NumericInteroperableConst) = e1 <= __wrap_const(e2)
Base.:<=(e1::NumericInteroperableConst, e2::NumericInteroperableExpr) = __wrap_const(e1) <= e2

Base.:(==)(e1::NumericInteroperableExpr, e2::NumericInteroperableExpr) = Base.:(==)(promote(e1, e2)...)
Base.:(==)(e1::NumericInteroperableExpr, e2::NumericInteroperableConst) = e1 == __wrap_const(e2)
Base.:(==)(e1::NumericInteroperableConst, e2::NumericInteroperableExpr) = __wrap_const(e1) == e2

distinct(e1::NumericInteroperableExpr, e2::NumericInteroperableExpr) = distinct(promote(e1, e2)...)
distinct(e1::NumericInteroperableExpr, e2::NumericInteroperableConst) = distinct(e1, __wrap_const(e2))
distinct(e1::NumericInteroperableConst, e2::NumericInteroperableExpr) = distinct(__wrap_const(e1), e2)
distinct(e1::NumericInteroperableConst, e2::NumericInteroperableConst) = e1 != e2


##### UNARY OPERATIONS #####
"""
    -(a::IntExpr)
    -(r::RealExpr)

Return the negative of an Int or Real expression.

```julia
@satvariable(a[1:n, 1:m], Int)
-a # this also works
```

"""
Base.:-(e::IntExpr) = IntExpr(:neg, IntExpr[e,], isnothing(e.value) ? nothing : -e.value, __get_hash_name(:neg, [e,]))
Base.:-(e::RealExpr) = RealExpr(:neg, RealExpr[e,], isnothing(e.value) ? nothing : -e.value, __get_hash_name(:neg, [e,]))

# Define array version for convenience because the syntax .- for unary operators is confusing.
Base.:-(es::Array{T}) where {T<:NumericExpr} = .-es

"""
    abs(a::IntExpr)
    
Return the absolute value of an `IntExpr`.

When called on a `RealExpr`, `abs(a::RealExpr)` returns `ite(a >= 0, a, -a)`. This design decision was made because Z3 allows `abs` to be called on a real-valued expression and returns that result, but `abs` is only defined in the SMT-LIB standard for integer variables. Thus, users may call `abs` on real-valued expressions.
"""
Base.abs(e::IntExpr) = IntExpr(:abs, IntExpr[e,], isnothing(e.value) ? nothing : -e.value, __get_hash_name(:abs, [e,]))
Base.abs(e::RealExpr) = ite(e >= 0.0, e, -e)
Base.abs(e::BoolExpr) = ite(e, 1, 0)

##### COMBINING OPERATIONS #####
# These return Int values. We would say they have sort Int.
# See figure 3.3 in the SMT-LIB standard.

# If literal is != 0, add a :const expr to es representing literal
function __add_const!(es::Array{T}, literal::Real) where {T<:AbstractExpr}
    if literal != 0
        const_expr = isa(literal, Float64) ? RealExpr(:const, AbstractExpr[], literal, "const_$literal") : IntExpr(:const, AbstractExpr[], literal, "const_$literal")
        push!(es, const_expr)
    end
end

# If there is more than one :const expr in es, merge them into one
function __merge_const!(es::Array{T}) where {T<:AbstractExpr}
    const_exprs = filter((e) -> e.op == :const, es)
    if length(const_exprs) > 1
        filter!((e) -> e.op != :const, es)
        __add_const!(es, sum(getproperty.(const_exprs, :value)))
    end
end

# This works for any n_ary op that takes as input NumericInteroperableExpr arguments
function __numeric_n_ary_op(es_mixed::Array, op::Symbol; __is_commutative=false, __try_flatten=false)
    # clean up types! This guarantees es::Array{AbstractExpr}
    es, literals = __check_inputs_nary_op(es_mixed, const_type=NumericInteroperableConst, expr_type=NumericInteroperableExpr)
    if all(isa.(es, BoolExpr)) # this can happen for example if you have Bool x + Bool z
        es[1] = ite(es[1], 1, 0) # convert one to IntExpr
        es = collect(promote(es...))
        literals = convert.(Int, literals)
    end

    literals = __is_commutative && length(literals) > 0 ? [sum(literals)] : literals

    # now we are guaranteed all es are valid exprs and all literals have been condensed to one
    for l in literals
        __add_const!(es, l)
    end

    # Determine return expr type. Note that / promotes to RealExpr because the SMT theory of integers doesn't include it
    ReturnType = any(isa.(es, RealExpr)) ? RealExpr : IntExpr
    children, name = __combine(es, op, __is_commutative, __try_flatten)

    # Now it is possible we have several CONST exprs. This occurs if, for example, one writes (a+1) + (b+1) which flattens to a+1+b+1
    # TO clean up, we should merge the CONST exprs
    if __is_commutative
        __merge_const!(children)
        name = __get_hash_name(op, children, is_commutative=__is_commutative)
    end
    # TODO should call a function indexed by op
    value = any(isnothing.(getproperty.(es, :value))) ? nothing : sum(getproperty.(es, :value))
    return ReturnType(op, children, value, name, __is_commutative=__is_commutative)
end


# The unsightly typing here specifies the following extensions to Base.:+
# NumericExpr + NumericExpr
# NumericExpr + Const
# Const + NumericExpr

"""
    a + b
    a + 1 + true

Return the `Int` | `Real` expression `a+b` (inherits the type of `a+b`). Use dot broadcasting for vector-valued and matrix-valued expressions.


```julia
@satvariable(a[1:n], Int)
@satvariable(b[1:n, 1:m], Int)
a .+ b
println("typeof a+b: \$(typeof(a[1] + b[1]))")

@satvariable(c, Real)
println("typeof a+c: \$(typeof(a[1] + c))")

@satvariable(z, Bool)
a .+ z
println("typeof a+z: \$(typeof(a[1] + z))")
```

"""
Base.:+(e1::NumericInteroperableExpr, e2::NumericInteroperableExpr) = __numeric_n_ary_op(collect(promote(e1, e2)), :add, __is_commutative=true, __try_flatten=true)
Base.:+(e1::NumericInteroperableExpr, e2::NumericInteroperableConst) = __numeric_n_ary_op([e1, e2], :add, __is_commutative=true, __try_flatten=true)
Base.:+(e1::NumericInteroperableConst, e2::NumericInteroperableExpr) = __numeric_n_ary_op([e1, e2], :add, __is_commutative=true, __try_flatten=true)

"""
    a - b
    a - 2

Returns the `Int` | `Real` expression `a-b` (inherits the type of `a-b`). Use dot broadcasting for vector-valued and matrix-valued expressions.

```julia
@satvariable(a[1:n], Int)
@satvariable(b[1:n, 1:m], Int)
a .- b
println("typeof a-b: \$(typeof(a[1] - b[1]))")

@satvariable(c, Real)
println("typeof a-c: \$(typeof(a[1] - c))")

@satvariable(z, Bool)
a .- z
println("typeof a-z: \$(typeof(a[1] - z))")
```
"""
Base.:-(e1::NumericInteroperableExpr, e2::NumericInteroperableExpr) = __numeric_n_ary_op(collect(promote(e1, e2)), :sub)
Base.:-(e1::NumericInteroperableExpr, e2::NumericInteroperableConst) = __numeric_n_ary_op([e1, e2], :sub)
Base.:-(e1::NumericInteroperableConst, e2::NumericInteroperableExpr) = __numeric_n_ary_op([e1, e2], :sub)

"""
    a * b
    a * 2

Returns the `Int` | `Real` multiplication expression `a*b` (inherits the type of `a*b`). Use dot broadcasting for vector-valued and matrix-valued expressions.

```julia
@satvariable(a[1:n], Int)
@satvariable(b[1:n, 1:m], Int)
a .* b
println("typeof a*b: \$(typeof(a[1]*b[1]))")

@satvariable(c, Real)
println("typeof a*c: \$(typeof(a[1]*c))")

@satvariable(z, Bool)
a .- z
println("typeof a*z: \$(typeof(a[1]*z))")
```
"""
Base.:*(e1::NumericInteroperableExpr, e2::NumericInteroperableExpr) = __numeric_n_ary_op(collect(promote(e1, e2)), :mul, __is_commutative=true, __try_flatten=true)
Base.:*(e1::NumericInteroperableExpr, e2::NumericInteroperableConst) = __numeric_n_ary_op([e1, e2], :mul, __is_commutative=true, __try_flatten=true)
Base.:*(e1::NumericInteroperableConst, e2::NumericInteroperableExpr) = __numeric_n_ary_op([e1, e2], :mul, __is_commutative=true, __try_flatten=true)

Base.:^(e::NumericInteroperableExpr, n::Int) = prod([e for i = 1:n])

"""
    div(a, b)
    div(a, 2)

Returns the `Int` division expression `div(a,b)`. Note: `a` and `b` will be converted to `IntExpr`. Use dot broadcasting for vector-valued and matrix-valued expressions.

```julia
@satvariable(a[1:n], Int)
@satvariable(b[1:n, 1:m], Int)
div.(a, b)
println("typeof div(a,b): \$(typeof(div(a[1],b[1])))")
```
"""
Base.div(e1::NumericInteroperableExpr, e2::NumericInteroperableExpr) = __numeric_n_ary_op([convert(IntExpr, e1), convert(IntExpr, e2)], :div)
Base.div(e1::NumericInteroperableExpr, e2::NumericInteroperableConst) = __numeric_n_ary_op([convert(IntExpr, e1), __wrap_const(Int(floor(e2)))], :div)
Base.div(e1::NumericInteroperableConst, e2::NumericInteroperableExpr) = __numeric_n_ary_op([__wrap_const(Int(floor(e1))), convert(IntExpr, e2)], :div)

"""
    mod(a, b)
    mod(a, 2)

Returns the `Int` modulus expression `mod(a,b)`. Note: `a` and `b` will be converted to `IntExpr`. Use dot broadcasting for vector-valued and matrix-valued expressions.
"""
Base.mod(e1::NumericInteroperableExpr, e2::NumericInteroperableExpr) = __numeric_n_ary_op([convert(IntExpr, e1), convert(IntExpr, e2)], :mod)
Base.mod(e1::NumericInteroperableExpr, e2::NumericInteroperableConst) = __numeric_n_ary_op([convert(IntExpr, e1), __wrap_const(Int(floor(e2)))], :mod)
Base.mod(e1::NumericInteroperableConst, e2::NumericInteroperableExpr) = __numeric_n_ary_op([__wrap_const(Int(floor(e1))), convert(IntExpr, e2)], :mod)

"""
    a / b
    a / 2.0

Returns the `Real` division expression `a/b`. Note: `a` and `b` will be converted to `RealExpr`. Use dot broadcasting for vector-valued and matrix-valued expressions.

```julia
@satvariable(a[1:n], Real)
@satvariable(b[1:n, 1:m], Real)
a ./ b
println("typeof a/b: \$(typeof(a[1]/b[1]))")
```
"""
Base.:/(e1::NumericInteroperableExpr, e2::NumericInteroperableExpr) = __numeric_n_ary_op([convert(RealExpr, e1), convert(RealExpr, e2)], :rdiv)
Base.:/(e1::NumericInteroperableExpr, e2::NumericInteroperableConst) = __numeric_n_ary_op([convert(RealExpr, e1), __wrap_const(Float64(e2))], :rdiv)
Base.:/(e1::NumericInteroperableConst, e2::NumericInteroperableExpr) = __numeric_n_ary_op([__wrap_const(Float64(e1)), convert(RealExpr, e2)], :rdiv)

Base.inv(e::NumericInteroperableExpr) = 1.0 / e # this performs the correct promotion due to the float 1.0

"""
    to_real(a::IntExpr)

Performs manual conversion of an IntExpr to a RealExpr. Note that Satisfiability.jl automatically promotes types in arithmetic and comparison expressions, so this function is usually unnecessary to explicitly call.
"""
to_real(a::IntExpr) = RealExpr(:to_real, [a], isnothing(a.value) ? nothing : Float64(a.value), __get_hash_name(:to_real, [a]))
to_real(a::RealExpr) = a # if we don't define this someone will call it and get a crash
to_real(a::Union{Number,Nothing}) = isnothing(a) ? nothing : Float64(a) # this is needed for __propagate_value! to correctly propagate values

"""
    to_int(a::RealExpr)

Performs manual conversion of a RealExpr to an IntExpr. Equivalent to Julia `Int(floor(a))`.
"""
to_int(a::RealExpr) = IntExpr(:to_int, [a], isnothing(a.value) ? nothing : Int(floor(a.value)), __get_hash_name(:to_int, [a]))
to_int(a::IntExpr) = a
to_int(a::Union{Number,Nothing}) = isnothing(a) ? nothing : Int(floor(a)) # this is needed for __propagate_value! to correctly propagate values

##### PROMOTION RULES #####
# These govern the promotion of BoolExpr, IntExpr and RealExpr types.
Base.promote_rule(::Type{IntExpr}, ::Type{BoolExpr}) = IntExpr
Base.promote_rule(::Type{RealExpr}, ::Type{BoolExpr}) = RealExpr
Base.promote_rule(::Type{RealExpr}, ::Type{IntExpr}) = RealExpr

Base.convert(::Type{IntExpr}, z::BoolExpr) = z.op == :const ? __wrap_const(Int64(z.value)) : ite(z, 1, 0)
Base.convert(::Type{RealExpr}, z::BoolExpr) = z.op == :const ? __wrap_const(Float64(z.value)) : ite(z, 1.0, 0.0)
Base.convert(::Type{RealExpr}, a::IntExpr) = a.op == :const ? __wrap_const(Float64(a.value)) : to_real(a)
Base.convert(::Type{IntExpr}, a::RealExpr) = a.op == :const ? __wrap_const(Int64(a.value)) : to_int(a)
