module BooleanSatisfiability

import Base.length, Base.size, Base.show, Base.string, Base.==, Base.broadcastable, Base.all, Base.any

export AbstractExpr, BoolExpr, ∧, ∨, ¬, ⟹, and, or, check_broadcastability, get_broadcast_shape, smt, smt!, declare, name, __get_combined_name, __get_hash_name, sat!, parse_smt_output, split_line, value

# Define the Variable object
abstract type AbstractExpr end

# op: :IDENTITY (variable only, no operation), :NOT, :AND, :OR
# children: BoolExpr children for an expression. And(z1, z2) has children [z1, z2]
# value: Bool array or nothing if result not computed
# name: String name of variable / expression. Can get long, we're working on that.
mutable struct BoolExpr <: AbstractExpr
    op       :: Symbol
    children :: Array{AbstractExpr}
    value    :: Union{Nothing, Bool}
    name     :: String
end

# https://stackoverflow.com/questions/32928524/julia-introspection-get-name-of-variable-passed-to-function
#macro __varname__(arg)
#    string(arg)
#end

Bool(name::String) :: BoolExpr                         = BoolExpr(:IDENTITY, Array{AbstractExpr}[], nothing, "$(name)")
Bool(n::Int, name::String) :: Vector{BoolExpr}         = [Bool("$(name)_$(i)") for i=1:n]
Bool(m::Int, n::Int, name::String) :: Matrix{BoolExpr} = [Bool("$(name)_$(i)_$(j)") for i=1:m, j=1:n]
# TODO use list complrehension with 2 dimensions

##### UTILITY FUNCTIONS #####

# Base calls
Base.size(e::BoolExpr) = 1
Base.length(e::AbstractExpr) = 1
Broadcast.broadcastable(e::AbstractExpr) = (e,)

# Printing behavior
# https://docs.julialang.org/en/v1/base/io-network/#Base.print
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

function is_permutation(a::Array, b::Array)
    return length(a) == length(b) && all(map( (c) -> c in b, a))
end

function (==)(expr1::BoolExpr, expr2::BoolExpr)
    return (expr1.op == expr2.op) && all(expr1.value .== expr2.value) && (expr1.name == expr2.name) && (is_permutation(expr1.children, expr2.children))
end

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


##### LOGICAL OPERATIONS #####

¬(z::BoolExpr)                        = BoolExpr(:NOT, [z], isnothing(z.value) ? nothing : !(z.value), __get_hash_name(:NOT, [z]))
¬(zs::Array{T}) where T <: BoolExpr   = map(¬, zs)
not(z::BoolExpr)                      = ¬z
not(z::Array{T}) where T <: BoolExpr  = ¬z 

∧(z1::AbstractExpr, z2::AbstractExpr) = and([z1, z2])
∨(z1::AbstractExpr, z2::AbstractExpr) = or([z1, z2])
⟹(z1::BoolExpr, z2::AbstractExpr)   = or([¬z1, z2])

function and(zs::Array{T}; broadcast_type=:Elementwise) where T <: AbstractExpr
    if length(zs) == 0
        return nothing
    elseif length(zs) == 1
        return zs[1]
    else
        child_values = map((z) -> z.value, zs)
        value = any(isnothing.(child_values)) ? nothing : reduce(&, child_values)
		return BoolExpr(:AND, zs, value, __get_hash_name(:AND, zs))
    end
end

# We need this extra line to enable the syntax and.([z1, z2,...,zn]) where z1, z2,...,zn are broadcast-compatible
and(zs::Vararg{T}; broadcast_type=:Elementwise) where T <: AbstractExpr = and(collect(zs))

function or(zs::Array{T}; broadcast_type=:Elementwise) where T <: AbstractExpr
    if length(zs) == 0
        error("Cannot iterate over zero-length array.")
    elseif length(zs) == 1
        return zs[1]
    else
        child_values = map((z) -> z.value, zs)
        value = any(isnothing.(child_values)) ? nothing : reduce(|, child_values)
        return BoolExpr(:OR, zs, value, __get_hash_name(:OR, zs))
    end
end

# We need this extra line to enable the syntax or.([z1, z2,...,zn]) where z1, z2,...,z are broadcast-compatible
or(zs::Vararg{T}; broadcast_type=:Elementwise) where T <: AbstractExpr = or(collect(zs))


##### ADDITIONAL OPERATIONS #####

flatten(a::Array{T}) where T = reshape(a, length(a))

"combine is used for both all() and any() since those are fundamentally the same with different operations."
function combine(zs::Array{T}, op::Symbol) where T <: BoolExpr
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

combine(zs::Matrix{T}, op::Symbol) where T <: BoolExpr = combine(flatten(zs), op)

all(zs::Array{T}) where T <: BoolExpr = combine(zs, :AND)
any(zs::Array{T}) where T <: BoolExpr = combine(zs, :OR)

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

function define_2op!(zs::Array{BoolExpr}, op::Symbol, cache::Dict{UInt64, String}, depth::Int) :: String
    if length(zs) == 0
        return ""
    elseif length(zs) == 1
        return "(assert ($(zs[1].name)))\n"
    else
        opname = op == :AND ? "and" : "or"
        fname = __get_hash_name(op, zs)
        declaration = "(define-fun $fname () Bool ($opname $(join(map( (c) -> c.name, zs), " "))))\n"
        prop = depth == 0 ? declaration*"(assert $fname)\n" : declaration
        cache_key = hash(declaration) # we use this to find out if we already declared this item

        if cache_key in keys(cache)
            prop = cache[cache_key]
        else
            prop = depth == 0 ? declaration*"(assert $fname)\n" : declaration
            cache[cache_key] = "(assert $fname)\n"
        end
        return prop
    end
end

function smt!(z::BoolExpr, declarations::Array{T}, propositions::Array{T}, cache::Dict{UInt64, String}, depth::Int) :: Tuple{Array{T}, Array{T}} where T <: String 
    if z.op == :IDENTITY
        n = length(declarations)
        push_unique!(declarations, declare(z))
    else
        map( (c) -> smt!(c, declarations, propositions, cache, depth+1) , z.children)

        if z.op == :NOT
            fname = __get_hash_name(:NOT, z.children)
            declaration = "(define-fun $fname () Bool (not $(z.children[1].name)))"
            cache_key = hash(declaration)
            if cache_key in keys(cache) && depth == 0
                prop = cache[cache_key]
                push!(propositions, prop)
            else
                if depth == 0
                    prop = declaration*"\n(assert $fname)\n"
                    push!(propositions,prop)
                else
                    push!(propositions, declaration)
                end
                cache[cache_key] = "(assert $fname)\n"
            end
        elseif (z.op == :AND) || (z.op == :OR)
            props = broadcast((zs::Vararg{BoolExpr}) -> define_2op!(collect(zs), z.op, cache, depth), z.children...)
            n = length(propositions)
            append_unique!(propositions, collect(props))
        else
            error("Unrecognized operation $(z.op)!")
        end
    end
    return declarations, propositions
end

function smt(z::BoolExpr) :: String
    declarations = String[]
    propositions = String[]
    cache = Dict{UInt64, String}()
    smt!(z, declarations, propositions,cache, 0)
    return reduce(*, declarations)*reduce(*,propositions)
end

function smt(zs::Array{T}) :: String where T <: BoolExpr
    if length(zs) == 1
        return smt(zs[1])
    else
        declarations = String[]
        propositions = String[]
        cache = Dict{UInt64, String}()
        map((z) -> smt!(z, declarations, propositions, cache, 0), zs) # old comment! # this is a 2 x n array where the first row is propositions and the second is declarations
        # this expression concatenates all the strings in row 1, then all the strings in row 2, etc.
        #declarations = reduce((l) -> append_unique!(declarations, l), strings[1,:])
        #propositions = reduce((l) -> append_unique!(propositions, l), strings[1,:])
        return join(declarations)*join(propositions)
    end
end


##### SOLVING THE PROBLEM #####

function sat!(zs::Vararg{Union{Array{T}, T}}; filename="out") :: Symbol where T <: BoolExpr
    if length(zs) == 0
        error("Empty problem")
    end

    # Combine the array exprs so we don't have arrays in arrays
    zs = map( (z) -> typeof(z) == BoolExpr ? z : all(z), zs)
    prob = and(zs...)

    open("$filename.smt", "w") do io
        write(io, smt(prob))
        write(io, "(check-sat)\n(get-model)\n")
    end
    status = :ERROR
    try
        output = read(`z3 -smt2 $filename.smt`, String)
        status, values = parse_smt_output(output)
        assign!(prob, values)
    catch e
        showerror(stdout, e)
        return status
    end
    return status
end

sat!(zs::Vector; filename="out") = sat!(zs...; filename)

# Split lines based on parentheses
function split_line(output, ptr)
    stack = 0
    while ptr < length(output)
        lp = findnext("(", output, ptr)
        rp = findnext(")", output, ptr)
        if isnothing(lp) || isnothing(rp)
            return nothing
        end
        lp, rp = lp[1], rp[1]
        if lp < rp
            ptr = lp+1 # move past the next (
            stack += 1
        else
            ptr = rp+1 # move past the next )
            stack -= 1
        end
        if stack == 0
            return ptr
        end
    end
end
function read_line!(line, values)
    line = join(filter( (c) -> c != '\n', line),"")
    line = split(line[1:end-1], " ") # strip ( and )
    name = line[4] # TODO fix
    if line[end] == "true"
        values[name] = true
    elseif line[end] == "false"
        values[name] = false
    end
end

function parse_smt_output(output::String)
    # the first line should either be sat or unsat
    ptr = findfirst("\n", output)[1]
    status = output[1:ptr-1] == "sat" ? :SAT : :UNSAT
    # after that, there's one line with just (
    ptr = findnext("(\n", output, ptr)[2] # skip it
    # lines 3 - n-1 are the model definitions
    next_ptr = ptr
    values = Dict{String, Bool}()
    while ptr < length(output)
        next_ptr = split_line(output, ptr)
        if isnothing(next_ptr)
            break
        end
        #println(output[ptr:next_ptr])
        read_line!(output[ptr:next_ptr], values)
        ptr = next_ptr
    end
    return status, values
    # line n is the closing )
    #for i=3:length(output)-1
        
end

function assign!(z::T, values::Dict{String, Bool}) where T <: BoolExpr
    if z.op == :IDENTITY && z.name ∈ keys(values)
        z.value = values[z.name]
    else
        map( (z) -> assign!(z, values), z.children)
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

value(zs::Array{T}) where T <: AbstractExpr = map( (z) -> z.value, zs)
value(z::AbstractExpr) = z.value

# Module end
end