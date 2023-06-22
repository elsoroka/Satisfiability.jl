##### GENERATING SMTLIB REPRESENTATION #####

"""
    declare(z)

Generate SMT variable declarations for all variables in BoolExpr z.

Examples:
* `declare(z1)` returns `"(declare-const z1 Bool)\\n"`
* `declare(and(z1, z2))` returns `"(declare-const z1 Bool)\\n(declare-const z2 Bool)\\n"`.
"""
function declare(z::BoolExpr)
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
    smt(z::BoolExpr)
    smt(z1,...,zn)
    smt([z1,...,zn])

Generate the SMT representation of `z` or `and(z1,...,zn)`.

When calling `smt([z1,...,zn])`, the array must have type `Array{BoolExpr}`. Note that list comprehensions do not preserve array typing. For example, if `z` is an array of `BoolExpr`, `[z[i] for i=1:n]` will be an array of type `Any`. To preserve the correct type, use `BoolExpr[z[i] for i=1:n]`.
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

##### WRITE TO FILE #####

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
