module BooleanSatisfiability

import Base.length, Base.size, Base.show, Base.string, Base.==

export AbstractExpr, BoolExpr, ∧, ∨, ¬, ⟹, and, or, check_broadcastability, get_broadcast_shape, smt, declare

# Define the Variable object
abstract type AbstractExpr end

mutable struct BoolExpr <: AbstractExpr
    op       :: Symbol
    children :: Array{AbstractExpr}
    shape    :: Tuple{Integer, Vararg{Integer}}
    value    :: Union{Nothing, Array{Bool}}
    name     :: String
end

# https://stackoverflow.com/questions/32928524/julia-introspection-get-name-of-variable-passed-to-function
#macro __varname__(arg)
#    string(arg)
#end

Bool(n::Int, name::String)         = BoolExpr(:Identity, Array{BoolExpr}[], (n,), nothing, name)
Bool(m::Int, n::Int, name::String) = BoolExpr(:Identity, Array{BoolExpr}[], (m,n), nothing, name)

# Base calls
Base.size(e::BoolExpr) = e.shape
Base.length(e::AbstractExpr) = prod(size(e))

# Printing behavior
# https://docs.julialang.org/en/v1/base/io-network/#Base.print
Base.show(io::IO, expr::AbstractExpr) = print(io, string(expr))

# This helps us print nested exprs
function Base.string(expr::BoolExpr, indent=0)
	if expr.op == :Identity	
		return "$(repeat(" | ", indent))$(expr.name) $(expr.shape) = $(expr.value)\n"
	else
		res = "$(repeat(" | ", indent))$(expr.op)\n"
		for e in expr.children
			res *= string(e, indent+1)
		end
		return res
	end
end

function is_permutation(a, b)
    return length(a) == length(b) && all(map( (c) -> c in b, a))
end

function (==)(expr1::BoolExpr, expr2::BoolExpr)
    return (expr1.op == expr2.op) && all(expr1.shape .== expr2.shape) &&
           all(expr1.value .== expr2.value) && (is_permutation(expr1.children, expr2.children))
end

# Logical expressions# Here are more expressions
¬(z::BoolExpr) = BoolExpr(:Not, [z,], z.shape, nothing, "!$(z.name)")
∧(z1::AbstractExpr, z2::AbstractExpr) = and(z1, z2)
∨(z1::AbstractExpr, z2::AbstractExpr) = or(z1, z2)
⟹(z1::BoolExpr, z2::AbstractExpr) = or(¬z1, z2)

# https://pytorch.org/docs/stable/notes/broadcasting.html
function get_broadcast_shape(shape1::Tuple{Integer, Vararg{Integer}}, shape2::Tuple{Integer, Vararg{Integer}})
    # ensure length(shape1) <= length(shape2)
    (shape1, shape2) = length(shape1) <= length(shape2) ? (shape1, shape2) : (shape2, shape1)
    # now we check broadcastability for (s1,...,sn), (t1,...,tn) by checking whether si = ti or either si = 1 or ti = 1
    # we must check in forward and reverse order to match the built-in behavior
    
    # check forward
    # ensure they have the same length by appending 1's
    shape1_long = (shape1..., ntuple(i -> 1, length(shape2)-length(shape1))...)
    success = true
    result = Integer[]
    for (si, ti) in zip(shape1_long, shape2)
        if si != 1 && ti != 1 && si != ti
            success = false
            break
        else
            push!(result, max(si, ti))
        end
    end
    if success
        return tuple(result...)
    end
    # check backward
    # ensure they have the same length by prepending 1's
    shape1_long = (ntuple(i -> 1, length(shape2)-length(shape1))..., shape1...)
    success = true
    result = Integer[]
    for (si, ti) in zip(reverse(shape1_long), reverse(shape2))
        if si != 1 && ti != 1 && si != ti
            success = false
            break
        else
            push!(result, max(si, ti))
        end
    end
    if success
        return tuple(reverse(result)...)
    end
    # failure case
    return nothing
end

# check for n shapes
function check_broadcastability(shapes::Array{T}; should_throw=false) where T <: Tuple{Integer, Vararg{Integer}}
    s = shapes[1]
    for i=2:length(shapes)
        s = get_broadcast_shape(s, shapes[i])
        if isnothing(s)
            if should_throw
                throw(DimensionMismatch("Unable to broadcast variables of shapes $(shapes[i-1]) and $(shapes[i]))"))
            else
                return nothing
            end
        end
    end
    return s
end

function and(zs::Vararg{T}) where T <: AbstractExpr
    if length(zs) == 0
        return nothing
    elseif length(zs) == 1
        return zs[1]
    else
        zs = collect(zs)
        shape = check_broadcastability(map(size, zs), should_throw=true)
		return BoolExpr(:And, zs, shape, nothing, "and_$(zs[1].name)_$(zs[end].name)")
    end
end

function or(zs::Vararg{T}) where T <: AbstractExpr
    if length(zs) == 0
        return nothing
    elseif length(zs) == 1
        return zs[1]
    else
        zs = collect(zs)
        shape = check_broadcastability(map(size, zs), should_throw=true)
        return BoolExpr(:Or, zs, shape, nothing, "or_$(zs[1].name)_$(zs[end].name)")
    end
end


##### SMTLIB SECTION #####
# I timed checking if something is in an array and it seems to be efficient for strings.
function push_unique!(array::Array{T}, item::T) where T
    return !(item  in array) ? push!(array, item) : array
end
function append_unique!(array1::Array{T}, array2::Array{T}) where T
    append!(array1, filter( (item) -> !(item in array1), array2))
end

function declare(z::BoolExpr)
    if length(z) == 1
        return "(declare-const $(z.name) Bool)"
    elseif length(size(z)) == 1
        return join(map( (i) -> "(declare-const $(z.name)_$i Bool)", 1:size(z)[1]), '\n')
    elseif length(size(z)) == 2
        declarations = []
        m,n = size(z)
        for i=1:m
            append_unique!(declarations, map( (j) -> "(declare-const $(z.name)_$(i)_$j Bool)", 1:size(z)[2]))
        end
        return join(declarations, '\n')
    else
        error("Invalid size $(z.shape) for variable!")
    end
    join(declarations, '\n')
end

function smt(z::BoolExpr, declarations::Array{T}, propositions::Array{T}) where T <: String
    if z.op == :Identity
        push!(declarations, declare(z))
    else
        map( (c) -> smt(c, declarations, propositions) , z.children)

        if z.op == :Not
            #push!(propositions, smt(z.children[1]))
        elseif z.op == :And
        elseif z.op == :Or
        else
            error("Unrecognized operation $(z.op)!")
        end
    end
    return join(declarations, '\n')
end

function smt(z::BoolExpr)
    declarations = String[]
    propositions = String[]
    declarations, propositions = smt(z, declarations, propositions)
    return cat(join(declarations, '\n'), join(propositions, '\n'), dims=1)



end