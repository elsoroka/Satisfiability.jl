# Mapping of Julia Expr types to SMT names. This is necessary because to distinguish from native types Bool, Int, Real, etc, we call ours BoolExpr, IntExpr, RealExpr, etc.
__smt_typestr(e::BoolExpr) = "Bool"
__smt_typestr(e::IntExpr) = "Int"
__smt_typestr(e::RealExpr) = "Real"
__smt_typestr(e::AbstractBitVectorExpr) = "(_ BitVec $(e.length))"

# Dictionary of opnames with n>=2 operands. This is necessary because not all opnames are valid symbols
# For example, iff is = and := is an invalid symbol.
function __smt_opnames(e::AbstractExpr)
    op = e.op
    if op ∈ keys(__smt_symbolic_ops)
       return __smt_symbolic_ops[op]
    elseif op ∈ keys(__smt_generated_ops)
        return __smt_generated_ops[op](e)
    else
       return op
    end
end
# These special cases arise because the SMT-LIB specification requires names to be ASCII
# thus we have to name these to successfully name things in (define-fun )
# but the SMT-LIB operators are symbolic.
__smt_symbolic_ops = Dict(
    :implies => "=>",
    :iff     => "=",
    :eq      => "=",
    :add     => "+",
    :sub     => "-",
    :mul     => "*",
    :div     => "/",
    :neg     => "-",
    :lt      => "<",
    :leq     => "<=",
    :geq     => ">=",
    :gt      => ">",
)

# These are extra-special cases where the operator name is not ASCII and has to be generated at runtime
__smt_generated_ops = Dict(
    :int2bv  => (e::AbstractBitVectorExpr) -> "(_ int2bv $(e.length))",
    :extract => (e::AbstractBitVectorExpr) -> "(_ extract $(last(e.range)-1) $(first(e.range)-1))",
)

# Finally, we provide facilities for correct encoding of consts
function __format_smt_const(exprtype::Type, c::AbstractExpr)
    # there's no such thing as a Bool const because all Bool consts are simplifiable
    if exprtype <: IntExpr || exprtype <: RealExpr
        return string(c.value) # automatically does the right thing for Ints and Reals
    elseif exprtype <: AbstractBitVectorExpr
        if c.length % 4 == 0 # can be a hex string
            return "#x$(string(c.value, base=16, pad=div(c.length,4)))"
        else
            return "#b$(string(c.value, base=2, pad=c.length))"
        end
    else
        error("Unable to encode constant $c for expression of type $exprtype.")
    end
end


##### GENERATING SMTLIB REPRESENTATION #####

"""
    declare(z; line_ending='\n')

Generate SMT variable declarations for a BoolExpr variable (operation = :identity).

Examples:
* `declare(a::IntExpr)` returns `"(declare-const a Int)\\n"`
* `declare(and(z1, z2))` returns `"(declare-const z1 Bool)\\n(declare-const z2 Bool)\\n"`.
"""
function declare(z::AbstractExpr; line_ending='\n')
    # There is only one variable
    vartype = __smt_typestr(z)
    if length(z) == 1
        return "(declare-const $(z.name) $vartype)$line_ending"
    # Variable is 1D
    elseif length(size(z)) == 1
        return join(map( (i) -> "(declare-const $(z.name)_$i $vartype)$line_ending", 1:size(z)[1]))
    # Variable is 2D
    elseif length(size(z)) == 2
        declarations = String[]
        # map over 2D variable rows, then cols inside
        m,n = size(z)
        map(1:m) do i
            append_unique!(declarations, map( (j) -> "(declare-const $(z.name)_$(i)_$j $vartype)$line_ending", 1:size(z)[2]))
        end
        return join(declarations)
    else
        error("Invalid size $(z.shape) for variable!")
    end
    join(declarations, line_ending)
end

declare(zs::Array{T}; line_ending='\n') where T <: AbstractExpr = reduce(*, declare.(zs; line_ending=line_ending))


# Return either z.name or the correct (as z.name Type) if z.name is defined for multiple types
# This multiple name misbehavior is allowed in SMT2; the expression (as z.name Type) is called a fully qualified name.
# It would arise if someone wrote something like @satvariable(x, Bool); x = xb; @satvariable(x, Int)
function __get_smt_name(z::AbstractExpr)
    if z.op == :const
        return __format_smt_const(typeof(z), z)
    end
    global GLOBAL_VARNAMES
    appears_in = map( (t) -> z.name ∈ GLOBAL_VARNAMES[t], __EXPR_TYPES)
    if sum(appears_in) > 1
        return "(as $(z.name) $(__smt_typestr(z)))"
    else # easy case, one variable with z.name is defined
        return z.name
    end
end

"__define_n_op! is a helper function for defining the SMT statements for n-ary ops where n >= 2.
cache is a Dict where each value is an SMT statement and its key is the hash of the statement. This allows us to avoid two things:
1. Redeclaring SMT statements, which causes the solver to emit errors.
2. Re-using named functions. For example if we \"(define-fun FUNC_NAME or(z1, z2))\" and then the expression or(z1, z2) re-appears later in the expression \"and(or(z1, z2), z3)\", we can write and(FUNC_NAME, z3)."
function __define_n_op!(z::T, cache::Dict{UInt64, String}, depth::Int; assert=true, line_ending='\n') where T <: AbstractExpr
    children = z.children
    if length(children) == 0 # silly case but we should handle it
        return ""
    end
    if assert && depth == 0 && typeof(z) != BoolExpr
        @warn("Cannot assert non-Boolean expression $z")
    end
    
    # done error checking
    #if length(children) == 1
    #    return assert && depth == 0 ? "(assert ($(children[1].name)))$line_ending" : ""
    #else
        fname = __get_hash_name(z.op, children, is_commutative=z.__is_commutative)
        # if the expr is a :const it will have a value (e.g. 2 or 1.5), otherwise use its name
        # This yields a list like String["z_1", "z_2", "1"].
        varnames = __get_smt_name.(children)
        outname = __smt_typestr(z)
        if z.__is_commutative
            varnames = sort(varnames)
        end
        declaration = "(define-fun $fname () $outname ($(__smt_opnames(z)) $(join(varnames, " "))))$line_ending"
        cache_key = hash(declaration) # we use this to find out if we already declared this item
        prop = ""
        if cache_key in keys(cache)
            prop = depth == 0 ? cache[cache_key] : ""
        else
            if assert && typeof(z) == BoolExpr && depth == 0
                prop = declaration*"(assert $fname)$line_ending"
                # the proposition is generated and cached now.
                cache[cache_key] = "(assert $fname)$line_ending"
            else
                prop = declaration
            end
        end
        return prop
   # end
end


function __define_1_op!(z::AbstractExpr, cache::Dict{UInt64, String}, depth::Int; assert=true, line_ending='\n')
    fname = __get_hash_name(z.op, z.children)
    outtype = __smt_typestr(z)
    prop = ""
    declaration = "(define-fun $fname () $outtype ($(__smt_opnames(z)) $(__get_smt_name(z.children[1]))))$line_ending"
    cache_key = hash(declaration)

    if assert && depth == 0 && typeof(z) != BoolExpr
        @warn("Cannot assert non-Boolean expression $z")
    end

    if cache_key in keys(cache) && depth == 0
        prop = cache[cache_key] # the proposition was already generated in a previous step
    else
        # if depth = 0 that means we are at the top-level of a nested expression.
        # thus, if the expr is Boolean we should assert it.
        if assert && typeof(z) == BoolExpr && depth == 0
            prop = declaration*"(assert $fname)$line_ending"
            # the proposition is generated and cached now.
            cache[cache_key] = "(assert $fname)$line_ending"
        else
            prop = declaration
        end
    end
    
    return prop
end


"smt!(prob, declarations, propositions) is an INTERNAL version of smt(prob).
We use it to iteratively build a list of declarations and propositions.
Users should call smt(prob, line_ending)."
function smt!(z::AbstractExpr, declarations::Array{T}, propositions::Array{T}, cache::Dict{UInt64, String}, depth::Int; assert=true, line_ending='\n') :: Tuple{Array{T}, Array{T}} where T <: String 
    if z.op == :identity # a single variable
        n = length(declarations)
        push_unique!(declarations, declare(z; line_ending=line_ending))
        if assert && depth == 0
            if typeof(z) != BoolExpr
                @warn("Cannot assert non-Boolean expression $z")
            else
                push_unique!(propositions, "(assert $(z.name))$line_ending")
            end
        end

    elseif z.op == :const
        ; # do nothing, constants don't need declarations

    else # an expression with operators and children
        map( (c) -> smt!(c, declarations, propositions, cache, depth+1, assert=assert, line_ending=line_ending) , z.children)

        if  length(z.children) == 1
            prop = __define_1_op!(z, cache, depth, assert=assert, line_ending=line_ending)

        else # all n-ary ops where n >= 2
            prop = __define_n_op!(z, cache, depth, assert=assert, line_ending=line_ending)
            #n = length(propositions)
        #else
        #   error("Unknown operation $(z.op)!")
        end

        push_unique!(propositions, prop)
    end
    return declarations, propositions
end


# Example:
# * `smt(and(z1, z2))` yields the statements `(declare-const z1 Bool)\n(declare-const z2 Bool)\n(define-fun AND_31df279ea7439224 Bool (and z1 z2))\n(assert AND_31df279ea7439224)\n`
"""
    smt(z::AbstractExpr; line_ending='\n')
    smt(z1,...,zn)
    smt([z1,...,zn])

Generate the SMT representation of `z` or `and(z1,...,zn)`.

When calling `smt([z1,...,zn])`, the array must have type `Array{AbstractExpr}`. Note that list comprehensions do not preserve array typing. For example, if `z` is an array of `BoolExpr`, `[z[i] for i=1:n]` will be an array of type `Any`. To preserve the correct type, use `BoolExpr[z[i] for i=1:n]`.
"""
function smt(zs::Array{T}; assert=true, line_ending=nothing) where T <: AbstractExpr
    if isnothing(line_ending)
        line_ending = Sys.iswindows() ? "\r\n" : '\n'
    end

    declarations = String[]
    propositions = String[]
    cache = Dict{UInt64, String}()
    if length(zs) == 1
        declarations, propositions = smt!(zs[1], declarations, propositions, cache, 0, assert=assert, line_ending=line_ending)
    else
        map((z) -> smt!(z, declarations, propositions, cache, 0, assert=assert, line_ending=line_ending), zs)
    end
    # this expression concatenates all the strings in row 1, then all the strings in row 2, etc.
    return reduce(*, declarations)*reduce(*,propositions)
end


smt(zs::Vararg{Union{Array{T}, T}}; assert=true, line_ending=nothing) where T <: AbstractExpr = smt(collect(zs), assert=assert, line_ending=line_ending)

##### WRITE TO FILE #####

"""
    save(z::AbstractExpr, filename; line_ending='\n')
    save(z::Array{AbstractExpr}, filename=filename, line_ending='\n')
    save(z1, z2,..., filename)                  # z1, z2,... are type AbstractExpr

Write the SMT representation of `z` or `and(z1,...,zn)` to filename.smt.
"""
function save(prob::AbstractExpr, filename="out"; assert=true, check_sat=true, line_ending=nothing)
    if isnothing(line_ending)
        line_ending = Sys.iswindows() ? "\r\n" : '\n'
    end

    if assert && typeof(prob) != BoolExpr
        @warn "Top-level expression must be Boolean to produce a valid SMT program."
    end
    open("$filename.smt", "w") do io
        write(io, smt(prob, assert=assert, line_ending=line_ending))
        if check_sat
            write(io, "(check-sat)$line_ending")
        end
    end
end

# this is the version that accepts a list of exprs, for example save(z1, z2, z3). This is necessary because if z1::BoolExpr and z2::Array{BoolExpr}, etc, then the typing is too difficult to make an array.
save(zs::Vararg{Union{Array{T}, T}}; filename="out", assert=true, check_sat=true, line_ending=nothing) where T <: AbstractExpr = save(__flatten_nested_exprs(all, zs...), filename, assert=assert, check_sat=check_sat, line_ending=line_ending)

# array version for convenience. THIS DOES NOT ACCEPT ARRAYS OF MIXED AbstractExpr and Array{AbstractExpr}.
save(zs::Array{T}, filename="out"; assert=true, check_sat=true, line_ending=nothing) where T <: AbstractExpr = save(all(zs), filename, assert=assert, check_sat=check_sat, line_ending=line_ending)
