import Base.length, Base.size, Base.show, Base.string, Base.isequal, Base.hash, Base.broadcastable

##### TYPE DEFINITIONS #####

# Define the Variable object
abstract type AbstractExpr end

# op: :IDENTITY (variable only, no operation), :NOT, :AND, :OR, :XOR, :IFF, :IMPLIES, :ITE (if-then-else)
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
function Bool(name::String) :: BoolExpr
	# This unsightly bit enables warning when users define two variables with the same string name.
	global GLOBAL_VARNAMES
	global WARN_DUPLICATE_NAMES
	if name ∈ GLOBAL_VARNAMES[BoolExpr]
        if WARN_DUPLICATE_NAMES @warn("Duplicate variable name $name of type Bool") end
    else
        push!(GLOBAL_VARNAMES[BoolExpr], name)
    end
	return BoolExpr(:IDENTITY, Array{AbstractExpr}[], nothing, "$(name)")
end
Bool(n::Int, name::String) :: Vector{BoolExpr}         = BoolExpr[Bool("$(name)_$(i)") for i=1:n]
Bool(m::Int, n::Int, name::String) :: Matrix{BoolExpr} = BoolExpr[Bool("$(name)_$(i)_$(j)") for i=1:m, j=1:n]


##### BASE FUNCTIONS #####

# Base calls
Base.size(e::AbstractExpr) = 1
Base.length(e::AbstractExpr) = 1
Broadcast.broadcastable(e::AbstractExpr) = (e,)

# Printing behavior https://docs.julialang.org/en/v1/base/io-network/#Base.print
Base.show(io::IO, expr::AbstractExpr) = print(io, string(expr))

# This helps us print nested exprs
function Base.string(expr::AbstractExpr, indent=0)::String
	if expr.op == :IDENTITY	
		return "$(repeat(" | ", indent))$(expr.name)$(isnothing(expr.value) ? "" : " = $(expr.value)")\n"
	else
		res = "$(repeat(" | ", indent))$(expr.name)$(isnothing(expr.value) ? "" : " = $(expr.value)")\n"
		for e in expr.children
			res *= string(e, indent+1)
		end
		return res
	end
end

"Test equality of two BoolExprs."
function Base.isequal(expr1::AbstractExpr, expr2::AbstractExpr)
    return (expr1.op == expr2.op) && all(expr1.value .== expr2.value) && (expr1.name == expr2.name) && (__is_permutation(expr1.children, expr2.children))
end

# Required for isequal apparently, since isequal(expr1, expr2) implies hash(expr1) == hash(expr2).
function Base.hash(expr::AbstractExpr)
    return hash("$(show(expr))")
end

# Overload because Base.in uses == which se used to construct equality expressions
function Base.in(expr::T, exprs::Array{T}) where T <: AbstractExpr
	return any(isequal.(expr, exprs))
end