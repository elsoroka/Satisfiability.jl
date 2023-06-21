module BooleanSatisfiability

import Base.length, Base.size, Base.show, Base.string, Base.==, Base.broadcastable, Base.all, Base.any

export AbstractExpr, BoolExpr, ∧, ∨, ¬, ⟹, and, or, not, implies, smt, declare, sat!, save, value


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

" Test equality of two BoolExprs"
function (==)(expr1::BoolExpr, expr2::BoolExpr)
    return (expr1.op == expr2.op) && all(expr1.value .== expr2.value) && (expr1.name == expr2.name) && (__is_permutation(expr1.children, expr2.children))
end


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

¬(z::BoolExpr)                        = BoolExpr(:NOT, [z], isnothing(z.value) ? nothing : !(z.value), __get_hash_name(:NOT, [z]))
¬(zs::Array{T}) where T <: BoolExpr   = map(¬, zs)
not(z::BoolExpr)                      = ¬z
not(z::Array{T}) where T <: BoolExpr  = ¬z 

∧(z1::BoolExpr, z2::BoolExpr) = and([z1, z2])
∨(z1::BoolExpr, z2::BoolExpr) = or([z1, z2])

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
    
Returns `and(z1,...,zn)`. If `z1,...,zn` are themselves `AND` operations, `all(z)`` flattens the nested `AND`.

Examples:
* `and([and(z1, z2), and(z3, z4)]) == and(z1, z2, z3, z4)`
* `and([or(z1, z3), z3, z4]) == and(or(z1, z3), z3, z4)`
"""
all(zs::Array{T}) where T <: BoolExpr = __combine(zs, :AND)

"""
    any([z1,...,zn])

Returns `or(z1,...,zn)`. If `z1,...,zn` are themselves `OR` operations, `any(z)`` flattens the nested `OR`.
Examples:
* `any([or(z1, z2), or(z3, z4)]) == or(z1, z2, z3, z4)`
* `any([and(z1, z3), z3, z4]) == or(and(z1, z3), z3, z4)`
"""
any(zs::Array{T}) where T <: BoolExpr = __combine(zs, :OR)


##### SMTLIB SECTION #####

:"""
    declare(z)

returns only the SMT commands that declare the variables in z.

Examples:
* declare(z1) returns `(declare-const z1 Bool)\n\`
* declare(and(z1, z2)) returns `(declare-const z1 Bool)\n(declare-const z2 Bool)\n`.
"""
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


"__define_2op is a helper function for defining the SMT statements for AND and OR.
op should be either :AND or :OR.
cache is a Dict where each value is an SMT statement and its key is the hash of the statement. This allows us to avoid two things:
1. Redeclaring SMT statements, which causes z3 to emit errors and is generally sloppy.
2. Re-using named functions. For example if we \"(define-fun FUNC_NAME or(z1, z2))\" and then the expression or(z1, z2) re-appears later in the expression \"and(or(z1, z2), z3)\", we can write and(FUNC_NAME, z3)."
function __define_2op!(zs::Array{BoolExpr}, op::Symbol, cache::Dict{UInt64, String}, depth::Int) :: String
    if length(zs) == 0
        return ""
    elseif length(zs) == 1
        return depth == 0 ? "(assert ($(zs[1].name)))\n" : ""
    else
        opname = op == :AND ? "and" : "or"
        fname = __get_hash_name(op, zs)
        varnames = map( (c) -> c.name, zs)

        declaration = "(define-fun $fname () Bool ($opname $(join(sort(varnames), " "))))\n"
        cache_key = hash(declaration) # we use this to find out if we already declared this item
        prop = ""
        if cache_key in keys(cache)
            prop = depth == 0 ? cache[cache_key] : ""
        else
            prop = depth == 0 ? declaration*"(assert $fname)\n" : declaration
            cache[cache_key] = "(assert $fname)\n"
        end
        return prop
    end
end


"smt!(prob, declarations, propositions) is an INTERNAL version of smt(prob).
We use it to iteratively build a list of declarations and propositions.
Users should call smt(prob)."
function smt!(z::BoolExpr, declarations::Array{T}, propositions::Array{T}, cache::Dict{UInt64, String}, depth::Int) :: Tuple{Array{T}, Array{T}} where T <: String 
    if z.op == :IDENTITY
        n = length(declarations)
        push_unique!(declarations, declare(z))
    else
        map( (c) -> smt!(c, declarations, propositions, cache, depth+1) , z.children)

        if z.op == :NOT
            fname = __get_hash_name(:NOT, z.children)
            declaration = "(define-fun $fname () Bool (not $(z.children[1].name)))\n"
            cache_key = hash(declaration)
            if cache_key in keys(cache) && depth == 0
                prop = cache[cache_key]
                push_unique!(propositions, prop)
            else
                if depth == 0
                    prop = declaration*"\n(assert $fname)\n"
                    push_unique!(propositions,prop)
                else
                    push_unique!(propositions, declaration)
                end
                cache[cache_key] = "(assert $fname)\n"
            end
        elseif (z.op == :AND) || (z.op == :OR)
            props = broadcast((zs::Vararg{BoolExpr}) -> __define_2op!(collect(zs), z.op, cache, depth), z.children...)
            n = length(propositions)
            append_unique!(propositions, collect(props))
        else
            error("Unrecognized operation $(z.op)!")
        end
    end
    return declarations, propositions
end


# Example:
# * `smt(and(z1, z2))` yields the statements `(declare-const z1 Bool)\n(declare-const z2 Bool)\n(define-fun AND_31df279ea7439224 Bool (and z1 z2))\n(assert AND_31df279ea7439224)\n`
"""
    smt(z1,...,zn)

Generates the SMT expressions necessary to define the problem.
`smt` DOES NOT add the command `(check-sat)``.

The syntax `smt([z1,...,zn])` is also valid, however `[z1,...,zn]` must be of type `Array{BoolExpr}`. Note that list comprehensions do not preserve array typing. For example, if `z` is an array of `BoolExpr`, `[z[i] for i=1:n]` will be an array of type `Any`. To preserve the correct type, use `BoolExpr[z[i] for i=1:n]`.
"""
function smt(zs::Array{T}) where T <: BoolExpr
    declarations = String[]
    propositions = String[]
    cache = Dict{UInt64, String}()
    if length(zs) == 1
        declarations, propositions = smt!(zs[1], declarations, propositions, cache, 0)
    else
        map((z) -> smt!(z, declarations, propositions, cache, 0), zs)
    end
    # this expression concatenates all the strings in row 1, then all the strings in row 2, etc.
    return reduce(*, declarations)*reduce(*,propositions)
end


smt(zs::Vararg{Union{Array{T}, T}}) where T <: BoolExpr = smt(collect(zs))


##### SOLVING THE PROBLEM #####

"""
    save(prob, filename=filename)

Writes the SMT expressions defining prob, including \"(check-sat)\", to filename.smt.
"""
function save(prob::BoolExpr; filename="out")
    open("$filename.smt", "w") do io
        write(io, smt(prob))
        write(io, "(check-sat)\n")
    end
end

# this is the version that accepts a list of exprs, for example save(z1, z2, z3)
"""
    save(z1, z2,..., filename=filename)

Accepts a variable number of BoolExprs. Equivalent to smt(and(z1, z2,...) filename). It writes the SMT expressions to define prob, including \"(check-sat)\", to filename.smt.
"""
save(zs::Vararg{Union{Array{T}, T}}; filename="out") where T <: BoolExpr = save(__flatten_nested_exprs(all, zs...), filename)


"""
    sat!(prob)
    
Generates the SMT expression for the problem, adds `(check-sat)` and calls Z3 to solve it. If the problem is SAT, it issues the command `(get-model)` to Z3 and parses the returned model to set the values of all `BoolExprs` in `prob`.

Possible return values are `:SAT`, `:UNSAT`, or `:ERROR`. `prob` is only modified to add Boolean values if the return value is `:SAT`.
"""
function sat!(prob::BoolExpr)
    smt_problem = smt(prob)*"(check-sat)\n"
    status, values, proc = talk_to_z3(smt_problem)
    # Only assign values if there are values. If status is :UNSAT or :ERROR, values will be an empty dict.
    if status == :SAT
        __assign!(prob, values)
    end
    # TODO we don't need it rn, we return it in case we do useful things with it later like requesting unsat cores and stuff
    kill(proc)
    return status
end

"""
    sat!(z1, z2,...)

Accepts a variable number of BoolExprs, for example `sat!(z1, z2, z3)`. This is equivalent to `sat!(and(z1, z2, z3))`.
"""
sat!(zs::Vararg{Union{Array{T}, T}}) where T <: BoolExpr = length(zs) > 0 ?
                                                           sat!(__flatten_nested_exprs(all, zs...)) :
                                                           error("Cannot solve empty problem (no expressions).")

                                                           # this version accepts an array of exprs and [exprs] (arrays), for example sat!([z1, z2, z3])
sat!(zs::Array) = sat!(zs...)


##### INVOKE AND TALK TO Z3 #####

function talk_to_z3(input::String)
    cmd = `z3 -smt2 -in`
    pstdin = Pipe()
    pstdout = Pipe()
    pstderr = Pipe()
    proc = run(pipeline(cmd,
                        stdin = pstdin, stdout = pstdout, stderr = pstderr),
                        wait = false)
    # now we have a pipe open that we can communicate to z3 with
    write(pstdin, input)
    write(pstdin, "\n") # in case the input is missing \n
    
    # read only the bytes in the buffer, otherwise it hangs
    output = String(readavailable(pstdout))
    
    if length(output) == 0 # this shouldn't happen, but I put this check in otherwise it will hang waiting to read
        @error "Unable to retrieve input from z3 (this should never happen)."
        return :ERROR, Dict{String, Bool}(), proc
    end

    if startswith(output, "unsat") # the problem was successfully given to Z3, but it is UNSAT
        return :UNSAT, Dict{String, Bool}(), proc

    elseif startswith(output, "sat") # the problem is satisfiable
        write(pstdin, "(get-model)\n")
        sleep(0.001) # IDK WHY WE NEED THIS BUT IF WE DON'T HAVE IT, pstdout HAS 0 BYTES BUFFERED 
        output = String(readavailable(pstdout))
        satisfying_assignment = __parse_smt_output(output)
        return :SAT, satisfying_assignment, proc

    else
        @error "Z3 encountered the error: $(output)"
        return :ERROR, Dict{String, Bool}(), proc
    end
end


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
    value([z1,...,zn])

Returns Array{Bool} if z has been set by calling sat!, or Array{nothing} if the value of z is unknown / unset.
It's possible to return an array of mixed Bool and nothing, for example if you have concatenated two variables and one doesn't appear in the problem, thus not being set.
"""
value(zs::Array{T}) where T <: AbstractExpr = map( (z) -> z.value, zs)

"""
    value(z)
    
Returns Bool if z has been set by calling sat!, or nothing if the value of z is unknown / unset.
"""
value(z::AbstractExpr) = z.value

# Module end
end