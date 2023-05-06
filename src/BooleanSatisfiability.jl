module BooleanSatisfiability

import Base.length, Base.size, Base.show, Base.string, Base.==, Base.broadcastable

export AbstractExpr, BoolExpr, ∧, ∨, ¬, ⟹, and, or, check_broadcastability, get_broadcast_shape, smt, declare, name

# Define the Variable object
abstract type AbstractExpr end

# op: :Identity (variable only, no operation), :Not, :And, :Or
# broadcast_type: :All, :Elementwise, :Na. Ignored if :NA, otherwise it tells us how to broadcast n-ary functions (And, Or) over Bool arrays.
# children: BoolExpr children for an expression. And(z1, z2) has children [z1, z2]
# shape: Tuple size of resulting expression
# value: Bool array or nothing if result not computed
# name: String name of variable / expression. Can get long, we're working on that.
mutable struct BoolExpr <: AbstractExpr
    op       :: Symbol
    #broadcast_type :: Symbol
    children :: Array{AbstractExpr}
    #shape    :: Tuple{Integer, Vararg{Integer}}
    value    :: Union{Nothing, Array{Bool}}
    name     :: String
end

# https://stackoverflow.com/questions/32928524/julia-introspection-get-name-of-variable-passed-to-function
#macro __varname__(arg)
#    string(arg)
#end

Bool(n::Int, name::String)         = map( (i) -> BoolExpr(:Identity, Array{AbstractExpr}[], nothing, "$(name)_$i"), 1:n)
Bool(m::Int, n::Int, name::String) = reshape(reduce(vcat, map( (i) -> Bool(n, "$(name)_$i"), 1:m)), (m,n))
Bool(name::String) = BoolExpr(:Identity, Array{AbstractExpr}[], nothing, "$(name)")

# Base calls
Base.size(e::BoolExpr) = 1
Base.length(e::AbstractExpr) = 1
Broadcast.broadcastable(e::AbstractExpr) = (e,)

# Printing behavior
# https://docs.julialang.org/en/v1/base/io-network/#Base.print
Base.show(io::IO, expr::AbstractExpr) = print(io, string(expr))

# This helps us print nested exprs
function Base.string(expr::BoolExpr, indent=0)
	if expr.op == :Identity	
		return "$(repeat(" | ", indent))$(expr.name)$(isnothing(expr.value) ? "" : "= $(expr.value)")\n"
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
    return (expr1.op == expr2.op) && all(expr1.value .== expr2.value) && (is_permutation(expr1.children, expr2.children))
end


# Logical expressions# Here are more expressions
¬(z::BoolExpr) = BoolExpr(:Not, [z,], nothing, "!$(z.name)")
¬(zs::Array{T}) where T <: BoolExpr = map(¬, zs)
∧(z1::AbstractExpr, z2::AbstractExpr) = and([z1, z2])
∨(z1::AbstractExpr, z2::AbstractExpr) = or([z1, z2])
⟹(z1::BoolExpr, z2::AbstractExpr) = or([¬z1, z2])

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

function and(zs::Array{T}; broadcast_type=:Elementwise) where T <: AbstractExpr
    if length(zs) == 0
        return nothing
    elseif length(zs) == 1
        return zs[1]
    else
        zs = collect(zs)
        #shape = check_broadcastability(map(size, zs), should_throw=true)
		return BoolExpr(:And, zs, nothing, "and_$(zs[1].name)...$(zs[end].name)")
    end
end

# We need this extra line to enable the syntax and.([z1, z2,...,zn]) where z1, z2,...,zn are broadcast-compatible
and(zs::Vararg{T}; broadcast_type=:Elementwise) where T <: AbstractExpr = and(collect(zs))

function or(zs::Array{T}; broadcast_type=:Elementwise) where T <: AbstractExpr
    if length(zs) == 0
        return nothing
    elseif length(zs) == 1
        return zs[1]
    else
        zs = collect(zs)
        #shape = check_broadcastability(map(size, zs), should_throw=true)
        return BoolExpr(:Or, zs, nothing, "or_$(zs[1].name)...$(zs[end].name)")
    end
end

# We need this extra line to enable the syntax or.([z1, z2,...,zn]) where z1, z2,...,z are broadcast-compatible
or(zs::Vararg{T}; broadcast_type=:Elementwise) where T <: AbstractExpr = or(collect(zs))


##### SMTLIB SECTION #####
# I timed checking if something is in an array and it seems to be efficient for strings.
function push_unique!(array::Array{T}, item::T) where T
    return !(item  in array) ? push!(array, item) : array
end
function append_unique!(array1::Array{T}, array2::Array{T}) where T
    append!(array1, filter( (item) -> !(item in array1), array2))
end

function declare(z::BoolExpr) :: String
    # There is only one variable
    if length(z) == 1
        return "(declare-const $(z.name) Bool)\n"
    # Variable is 1D
    elseif length(size(z)) == 1
        return join(map( (i) -> "(declare-const $(z.name)_$i Bool)\n", 1:size(z)[1]))
    # Variable is 2D
    elseif length(size(z)) == 2
        declarations = String[]
        # map over 2D variable rows, then cols inside
        m,n = size(z)
        map(1:m) do i
            append_unique!(declarations, map( (j) -> "(declare-const $(z.name)_$(i)_$j Bool)\n", 1:size(z)[2]))
        end
        return join(declarations)
    else
        error("Invalid size $(z.shape) for variable!")
    end
    join(declarations, '\n')
end

function define_2op(zs::Array{BoolExpr}, op::Symbol, cache::Dict{String, String})::String
    if length(zs) == 0
        return ""
    elseif length(zs) == 1
        return "(assert ($(zs[1].name)))\n"
    else
        opname = op == :And ? "and" : "or"
        fname = "$opname_$(join(map( (c) -> c.name, zs), "_"))\n"
        if fname in keys(cache)
            prop = cache[fname]
        else
            prop = "(define-fun $fname () Bool ($opname $(join(map( (c) -> c.name, zs), " ")))\nassert ($fname)\n"
            cache[fname] = "assert ($fname)\n"
        end
        return prop
    end
end

function smt(z::BoolExpr, declarations::Array{T}, propositions::Array{T}) :: Tuple{Array{T}, Array{T}} where T <: String 
    cache = Dict{String, String}()
    if z.op == :Identity
        push!(declarations, declare(z))
    else
        map( (c) -> smt(c, declarations, propositions) , z.children)

        if z.op == :Not
            push!(propositions, "assert (not $(z.children[1].name))\n")
        elseif (z.op == :And) || (z.op == :Or)
            props = broadcast((x,y) -> define_2op([x,y], z.op, cache), z.children...)
            append(propositions, reshape(props, (length(props),)))
        else
            error("Unrecognized operation $(z.op)!")
        end
    end
    return declarations, propositions
end

function smt(z::BoolExpr) :: String
    declarations = String[]
    propositions = String[]
    declarations, propositions = smt(z, declarations, propositions)
    return join(declarations, '\n')*join(propositions, '\n')
end


end