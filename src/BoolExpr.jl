import Base.length, Base.size, Base.show, Base.string, Base.isequal, Base.hash, Base.in, Base.broadcastable

##### TYPE DEFINITIONS #####

# Define the Variable object
abstract type AbstractExpr end

# op: :identity (variable only, no operation), :not, :and, :or, :xor, :iff, :implies, :ite (if-then-else)
# children: BoolExpr children for an expression. And(z1, z2) has children [z1, z2]
# value: Bool array or nothing if result not computed
# name: String name of variable / expression.
# __ret_type : Corresponds to the sort of an operator in SMT-LIB. Necessitated because Julia has a dynamic type system so the compiler can't easily infer return type of an operator.
# __is_commutative: true if AbstractExpr is a commutative operator, false if not.
mutable struct BoolExpr <: AbstractExpr
    op       :: Symbol
    children :: Array{AbstractExpr}
    value    :: Union{Bool, Nothing, Missing}
    name     :: String
	__ret_type       :: Type
	__is_commutative :: Bool

	# for convenience
	BoolExpr(op::Symbol,
			children::Array{T},
			value::Union{Bool, Nothing, Missing},
			name::String;
			__ret_type = BoolExpr,
			__is_commutative = false) where T <: AbstractExpr = new(op, children, value, name, __ret_type, __is_commutative)
end


##### CONSTRUCTORS #####

"""
BoolExpr("z")

Construct a single Boolean variable with name "z".
"""
function BoolExpr(name::String) :: BoolExpr
	# This unsightly bit enables warning when users define two variables with the same string name.
	global GLOBAL_VARNAMES
	global WARN_DUPLICATE_NAMES
	if name ∈ GLOBAL_VARNAMES[BoolExpr]
        if WARN_DUPLICATE_NAMES @warn("Duplicate variable name $name of type Bool") end
    else
        push!(GLOBAL_VARNAMES[BoolExpr], name)
    end
	return BoolExpr(:identity, AbstractExpr[], nothing, "$(name)")
end
# may eventually be removed in favor of macros
#Bool(n::Int, name::String) :: Vector{BoolExpr}         = BoolExpr[Bool("$(name)_$(i)") for i=1:n]
#Bool(m::Int, n::Int, name::String) :: Matrix{BoolExpr} = BoolExpr[Bool("$(name)_$(i)_$(j)") for i=1:m, j=1:n]


##### BASE FUNCTIONS #####

# Base calls
Base.size(e::AbstractExpr) = 1
Base.length(e::AbstractExpr) = 1
Broadcast.broadcastable(e::AbstractExpr) = (e,)

# Printing behavior https://docs.julialang.org/en/v1/base/io-network/#Base.print
Base.show(io::IO, expr::AbstractExpr) = print(io, string(expr))

# This helps us print nested exprs
function Base.string(expr::AbstractExpr, indent=0)::String
	if expr.op == :identity	
		return "$(repeat(" | ", indent))$(expr.name)$(isnothing(expr.value) ? "" : " = $(expr.value)")\n"
	else
		res = "$(repeat(" | ", indent))$(expr.name)$(isnothing(expr.value) ? "" : " = $(expr.value)")\n"
		for e in expr.children
			res *= string(e, indent+1)
		end
		return res
	end
end

"Test equality of two AbstractExprs. To construct an equality constraint, use `==`."
function Base.isequal(expr1::AbstractExpr, expr2::AbstractExpr)
    return (expr1.op == expr2.op) &&
		   all(expr1.value .== expr2.value) &&
		   (expr1.name == expr2.name) &&
		   (expr1.__is_commutative ? __is_permutation(expr1.children, expr2.children) : ((length(expr1.children) == length(expr2.children)) && all(isequal.(expr1.children, expr2.children))))
end

# Required for isequal apparently, since isequal(expr1, expr2) implies hash(expr1) == hash(expr2).
function Base.hash(expr::AbstractExpr)
    return hash("$(show(expr))")
end

# Overload because Base.in uses == which se used to construct equality expressions
function Base.in(expr::T, exprs::Array{T}) where T <: AbstractExpr
	return any(isequal.(expr, exprs))
end