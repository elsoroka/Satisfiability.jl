module BooleanSatisfiability

import Base.length, Base.size, Base.show, Base.string, Base.==, Base.broadcastable, Base.all, Base.any

export AbstractExpr, BoolExpr, ∧, ∨, ¬, ⟹, and, or, not, implies, smt, declare, sat!, save, value

include("call_solver.jl")

##### TYPE DEFINITIONS #####

# Define the Variable object
abstract type AbstractExpr end

# op: :IDENTITY (variable only, no operation), :NOT, :AND, :OR
# children: BoolExpr children for an expression. And(z1, z2) has children [z1, z2]
# value: Bool array or nothing if result not computed
# name: String name of variable / expression. Can get long, we're working on that.
mutable struct BoolExpr <: AbstractExpr
    op       :: Symbol
    children :: Array{AbstractExpr}
    value    :: Union{Bool, Nothing, Missing}
    name     :: String
end

# define a type that accepts Array{T, Bool}, Array{Bool}, and Array{T}
# ExprArray{T} = Union{Array{Union{T, Bool}}, Array{T}, Array{Bool}}

##### CONSTRUCTORS #####

"""
    Bool("z")

Construct a single Boolean variable with name "z".

```julia
    Bool(n, "z")
    Bool(m, n, "z")
```

Construct a vector-valued or matrix-valued Boolean variable with name "z".

Vector and matrix-valued Booleans use Julia's built-in array functionality: calling `Bool(n,"z")` returns a `Vector{BoolExpr}`, while calling `Bool(m, n, "z")` returns a `Matrix{BoolExpr}`.
"""
Bool(name::String) :: BoolExpr                         = BoolExpr(:IDENTITY, Array{AbstractExpr}[], nothing, "$(name)")
Bool(n::Int, name::String) :: Vector{BoolExpr}         = [Bool("$(name)_$(i)") for i=1:n]
Bool(m::Int, n::Int, name::String) :: Matrix{BoolExpr} = [Bool("$(name)_$(i)_$(j)") for i=1:m, j=1:n]


##### BASE FUNCTIONS #####

# Base calls
Base.size(e::BoolExpr) = 1
Base.length(e::AbstractExpr) = 1
Broadcast.broadcastable(e::AbstractExpr) = (e,)

# Printing behavior https://docs.julialang.org/en/v1/base/io-network/#Base.print
Base.show(io::IO, expr::AbstractExpr) = print(io, string(expr))

# This helps us print nested exprs
function Base.string(expr::BoolExpr, indent=0)::String
	if expr.op == :IDENTITY	
		return "$(repeat(" | ", indent))$(expr.name)$(isnothing(expr.value) ? "" : "= $(expr.value)")\n"
	else
		res = "$(repeat(" | ", indent))$(expr.name)$(isnothing(expr.value) ? "" : "= $(expr.value)")\n"
		for e in expr.children
			res *= string(e, indent+1)
		end
		return res
	end
end

"Test equality of two BoolExprs."
function (==)(expr1::BoolExpr, expr2::BoolExpr)
    return (expr1.op == expr2.op) && all(expr1.value .== expr2.value) && (expr1.name == expr2.name) && (__is_permutation(expr1.children, expr2.children))
end

include("utilities.jl")
include("smt_representation.jl")

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
    names = sort(vec(map( (e)-> e.name, zs )))
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
    

##### LOGICAL OPERATIONS #####

"""
    not(z::BoolExpr)
    ¬z

Return the logical negation of `z`.
    
Note: Broacasting a unary operator requires the syntax `.¬z` which can be confusing to new Julia users. We define `¬(z::Array{BoolExpr})` for convenience.

```julia
    z = Bool(n, "z")
    ¬z  # syntactic sugar for map(¬, z)
    .¬z # also valid
```

"""
¬(z::BoolExpr)                        = BoolExpr(:NOT, [z], isnothing(z.value) ? nothing : !(z.value), __get_hash_name(:NOT, [z]))
¬(zs::Array{T}) where T <: BoolExpr   = map(¬, zs)
not(z::BoolExpr)                      = ¬z
not(z::Array{T}) where T <: BoolExpr  = ¬z 

"""
    z1 ∧ z2
    and(z1,...,zn)
    and([z1,...,zn])

Returns the logical AND of two or more variables. Use dot broadcasting for vector-valued and matrix-valued Boolean expressions.

```julia
z1 = Bool(n, "z1")
z2 = Bool(m, n, "z2")
z1 .∧ z2
and.(z1, z2) # equivalent to z1 .∧ z2
```

Special cases:
* `and(z)` returns `z`.
* `and(z, false)` returns `false`.
* `and(z, true)` returns `z`.
"""
∧(z1::BoolExpr, z2::BoolExpr) = and([z1, z2])

"""
    z1 ∨ z2
    or(z1,...,zn)
    or([z1,...,zn])

Returns the logical OR of two or more variables. Use dot broadcasting for vector-valued and matrix-valued Boolean expressions.

```julia
z1 = Bool(n, "z1")
z2 = Bool(m, n, "z2")
z1 .∨ z2
or.(z1, z2) # equivalent to z1 .∨ z2
```

Special cases:
* `or(z)` returns `z`.
* `or(z, false)` returns `z`.
* `or(z, true)` returns `true`.

**Note that ∨ (`\\vee`) is NOT the ASCII character v.**
"""
∨(z1::BoolExpr, z2::BoolExpr) = or([z1, z2])

"""
    z1 ⟹ z2
    implies(z1, z2)

Returns the expression z1 IMPLIES z2. Use dot broadcasting for vector-valued and matrix-valued Boolean expressions. Note: `implies(z1, z2)` is equivalent to `or(not(z1), z2)`.
"""
⟹(z1::BoolExpr, z2::BoolExpr)   = or([¬z1, z2])
implies(z1::BoolExpr, z2::BoolExpr) = ⟹(z1, z2)


function and(zs_mixed::Array{T}; broadcast_type=:Elementwise) where T
    
    if any((z) -> !(isa(z, Bool) || isa(z, BoolExpr)), zs_mixed)
        error("Unrecognized type in list")
    end
    # separate literals and BoolExpr
    literals = filter((z) -> isa(z, Bool), zs_mixed)
    zs = Array{AbstractExpr}(filter((z) -> isa(z, AbstractExpr), zs_mixed))

    if length(literals) > 0
        if !all(literals) # if any literal is 0
            return false
        elseif length(zs) == 0 # only literals, all of them must be true
            return true
        end
    end
    # having passed this processing of literals, we'll check for base cases
    if length(zs) == 0
        return nothing
    elseif length(zs) == 1
        return zs[1]
    end    

    # now the remaining are BoolExpr
    child_values = map((z) -> z.value, zs)
    value = any(isnothing.(child_values)) ? nothing : reduce(&, child_values)
    return BoolExpr(:AND, zs, value, __get_hash_name(:AND, zs))
end

# We need this extra line to enable the syntax and.([z1, z2,...,zn]) where z1, z2,...,zn are broadcast-compatible
and(zs::Vararg{Union{T, Bool}}; broadcast_type=:Elementwise) where T <: AbstractExpr = and(collect(zs))


function or(zs_mixed::Array{T}; broadcast_type=:Elementwise) where T
    # check for type correctness
    if any((z) -> !(isa(z, Bool) || isa(z, BoolExpr)), zs_mixed)
        error("Unrecognized type in list")
    end

    # separate literals and BoolExpr
    literals = filter((z) -> isa(z, Bool), zs_mixed)
    zs = Array{AbstractExpr}(filter((z) -> isa(z, AbstractExpr), zs_mixed))

    if length(literals) > 0
        if any(literals) # if any literal is 1
            return true
        elseif length(zs) == 0 # only literals, all of them must be false
            return false
        end
    end
    # having passed this processing of literals, we'll check for base cases
    if length(zs)== 0
        return nothing
    elseif length(zs) == 1
        return zs[1]
    end

    child_values = map((z) -> z.value, zs)
    value = any(isnothing.(child_values)) ? nothing : reduce(|, child_values)
    return BoolExpr(:OR, zs, value, __get_hash_name(:OR, zs))
end

# We need this extra line to enable the syntax or.([z1, z2,...,zn]) where z1, z2,...,z are broadcast-compatible
or(zs::Vararg{Union{T, Bool}}; broadcast_type=:Elementwise) where T <: AbstractExpr = or(collect(zs))


##### SUPPORT FOR OPERATIONS WITH MIXED LITERALS #####

not(z::Bool) = !z
not(zs::Array{T}) where T <: Bool = not.(zs)
not(zs::BitArray) = not.(zs)

¬(z::Bool)   = not(z)
¬(zs::Array{T})   where T <: Bool = not.(zs)
¬(zs::BitArray) = not.(zs)

∧(z1::BoolExpr, z2::Bool) = z2 ? z1 : false # returns z1 if z2 == true and false if z2 == false
∧(z1::Bool, z2::BoolExpr) = z1 ? z2 : false
∧(z1::Bool, z2::Bool) = z1 & z2

∨(z1::BoolExpr, z2::Bool) = z2 ? true : z1 # return true if z2 == true and z1 if z2 == false
∨(z1::Bool, z2::BoolExpr) = z1 ? true : z2
∨(z1::Bool, z2::Bool) = z1 | z2

⟹(z1::Union{BoolExpr, Bool}, z2::Union{BoolExpr, Bool}) = or([¬z1, z2])
implies(z1::Union{BoolExpr, Bool}, z2::Union{BoolExpr, Bool}) = ⟹(z1, z2)


##### ADDITIONAL OPERATIONS #####

"combine is used for both all() and any() since those are fundamentally the same with different operations."
function __combine(zs::Array{T}, op::Symbol) where T <: BoolExpr
    if length(zs) == 0
        error("Cannot iterate over zero-length array.")
    elseif length(zs) == 1
        return zs[1]
    end
    # Now we need to take an array of statements and...
    # (1) Verify they are all the same operator
    if !all(map( (e) -> e.op, zs) .== zs[1].op)
        error("Cannot combine array with mismatched operations.")
    end
    # (2) Combine them
    if zs[1].op == :IDENTITY
        name = __get_hash_name(op, zs)#"$(op)_$(__get_name_stem(zs))"
        children = flatten(zs)
    elseif zs[1].op == op
        # if op matches (e.g. any(or(z1, z2)) or all(and(z1, z2))) then flatten it.
        # (3) Returm a combined operator
        # this line gets a list with no duplicates of all children
        children = union(cat(map( (e) -> flatten(e.children), zs)..., dims=1))
        name = __get_hash_name(op, children)
    else # op doesn't match, so we won't flatten it but will combine all the children
        name = __get_hash_name(op, zs)
        children = flatten(zs)
    end

    return BoolExpr(op, children, nothing, name)
end

"combine(z, op) where z is an n x m matrix of BoolExprs first flattens z, then combines it with op.
combine([z1 z2; z3 z4], or) = or([z1; z2; z3; z4])."
__combine(zs::Matrix{T}, op::Symbol) where T <: BoolExpr = __combine(flatten(zs), op)

"""
    all([z1,...,zn])
    
Return `and(z1,...,zn)`. If `z1,...,zn` are themselves `AND` operations, `all(z)`` flattens the nested `AND`.

Examples:
* `and([and(z1, z2), and(z3, z4)]) == and(z1, z2, z3, z4)`
* `and([or(z1, z3), z3, z4]) == and(or(z1, z3), z3, z4)`
"""
all(zs::Array{T}) where T <: BoolExpr = __combine(zs, :AND)

"""
    any([z1,...,zn])

Return `or(z1,...,zn)`. If `z1,...,zn` are themselves `OR` operations, `any(z)`` flattens the nested `OR`.
Examples:
* `any([or(z1, z2), or(z3, z4)]) == or(z1, z2, z3, z4)`
* `any([and(z1, z3), z3, z4]) == or(and(z1, z3), z3, z4)`
"""
any(zs::Array{T}) where T <: BoolExpr = __combine(zs, :OR)


##### SOLVING THE PROBLEM #####

"""
    save(z::BoolExpr, filename=filename)
    save(z1, z2,..., filename=filename)

Write the SMT representation of `z` or `and(z1,...,zn)` to filename.smt.
"""
function save(prob::BoolExpr; filename="out")
    open("$filename.smt", "w") do io
        write(io, smt(prob))
        write(io, "(check-sat)\n")
    end
end

# this is the version that accepts a list of exprs, for example save(z1, z2, z3)
save(zs::Vararg{Union{Array{T}, T}}; filename="out") where T <: BoolExpr = save(__flatten_nested_exprs(all, zs...), filename)


"""
    sat!(z::BoolExpr)
    sat!(z1, z2,...)
    
Solve the SAT problem using Z3. If the problem is satisfiable, update the values of all `BoolExprs` in `prob` with their satisfying assignments.

Possible return values are `:SAT`, `:UNSAT`, or `:ERROR`. `prob` is only modified to add Boolean values if the return value is `:SAT`.
"""
function sat!(prob::BoolExpr)
    smt_problem = smt(prob)*"(check-sat)\n"
    status, values, proc = talk_to_solver(smt_problem)
    # Only assign values if there are values. If status is :UNSAT or :ERROR, values will be an empty dict.
    if status == :SAT
        __assign!(prob, values)
    end
    # TODO we don't need it rn, we return it in case we do useful things with it later like requesting unsat cores and stuff
    kill(proc)
    return status
end

sat!(zs::Vararg{Union{Array{T}, T}}) where T <: BoolExpr = length(zs) > 0 ?
                                                           sat!(__flatten_nested_exprs(all, zs...)) :
                                                           error("Cannot solve empty problem (no expressions).")

                                                           # this version accepts an array of exprs and [exprs] (arrays), for example sat!([z1, z2, z3])
sat!(zs::Array) = sat!(zs...)


function __assign!(z::T, values::Dict{String, Bool}) where T <: BoolExpr
    if z.op == :IDENTITY
        if z.name ∈ keys(values)
            z.value = values[z.name]
        else
            z.value = missing # this is better than nothing because & and | automatically skip it (three-valued logic).
        end
    else
        map( (z) -> __assign!(z, values), z.children)
        if z.op == :NOT
            z.value = !(z.children[1].value)
        elseif z.op == :AND
            z.value = reduce(&, map((c) -> c.value, z.children))
        elseif z.op == :OR
            z.value = reduce(|, map((c) -> c.value, z.children))
        else
            error("Unrecognized operator $(z.op)")
        end
    end
end

"""
    value(z::BoolExpr)
    value([z1,...,zn])

Returns the satisfying assignment of `z`, or `nothing` if no satisfying assignment is known. In the array-valued case, returns `Array{Bool}` or `Array{nothing}`.

It's possible to return an array of mixed `Bool` and `nothing`. This could occur if some variables in an array do not appear in a problem, because `sat!(problem)` will not set the values of variables that do not appear in `problem`.
"""
value(zs::Array{T}) where T <: AbstractExpr = map( (z) -> z.value, zs)

value(z::AbstractExpr) = z.value

# Module end
end