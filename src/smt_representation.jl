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
    :rdiv    => "/",
    :neg     => "-",
    :lt      => "<",
    :leq     => "<=",
    :geq     => ">=",
    :gt      => ">",
)

# These are extra-special cases where the operator name is not ASCII and has to be generated at runtime
__smt_generated_ops = Dict(
    :int2bv       => (e::AbstractBitVectorExpr) -> "(_ int2bv $(e.length))",
    :extract      => (e::SlicedBitVectorExpr)   -> "(_ extract $(last(e.range)-1) $(first(e.range)-1))",
    :repeat       => (e::SlicedBitVectorExpr)   -> "(_ repeat $(e.range))",
    :zero_extend  => (e::SlicedBitVectorExpr)   -> "(_ zero_extend $(e.range))",
    :sign_extend  => (e::SlicedBitVectorExpr)   -> "(_ sign_extend $(e.range))",
    :rotate_left  => (e::SlicedBitVectorExpr)   -> "(_ rotate_left $(e.range))",
    :rotate_right => (e::SlicedBitVectorExpr)   -> "(_ rotate_right $(e.range))",
    :ufunc        => (e::AbstractExpr) -> split(e.name, "_")[1]
)

# Finally, we provide facilities for correct encoding of consts
function __format_smt_const(exprtype::Type, c::AbstractExpr)
    # there's no such thing as a Bool const because all Bool consts are simplifiable
    if exprtype <: IntExpr || exprtype <: RealExpr || exprtype <: BoolExpr
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

#=
    declare(z; line_ending='\n')

Generate SMT variable declarations for a BoolExpr variable (operation = :identity).

Examples:
* `declare(a::IntExpr)` returns `"(declare-fun a () Int)\\n"`
* `declare(and(z1, z2))` returns `"(declare-fun z1 () Bool)\\n(declare-fun z2 () Bool)\\n"`.
=#
function declare(z::AbstractExpr; line_ending='\n')
    return "(declare-fun $(z.name) () $(__smt_typestr(z)))"
end

declare(zs::Array{T}) where T <: AbstractExpr = reduce(*, declare.(zs; line_ending=line_ending))

function declare_ufunc(e::AbstractExpr)
        name = e.children[1].name
        intype = __smt_typestr(e.children[2])
        outtype = __smt_typestr(e)
        return "(declare-fun $name($intype) $outtype)"
end

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


#=smt!(prob, declarations, propositions) is an INTERNAL version of smt(prob).
We use it to iteratively build a list of declarations and propositions.
Users should call smt(prob, line_ending).=#
function smt!(z::AbstractExpr, declarations::Array{T}, propositions::Array{T}, cache::Dict{UInt64, String}, depth::Int; assert=true) where T <: String 
    if z.op == :identity # a single variable
        #n = length(declarations)
        push_unique!(declarations, declare(z))
        if assert && depth == 0
            if typeof(z) != BoolExpr
                @warn("Cannot assert non-Boolean expression $z")
            else
                push_unique!(propositions, "(assert $(z.name))")
            end
        end
        prop = __get_smt_name(z)

    elseif z.op == :const
        prop = __format_smt_const(typeof(z), z)

    elseif z.op == :ufunc

        push_unique!(declarations, declare_ufunc(z))
        child_prop = smt!(z.children[2], declarations, propositions, cache, depth+1, assert=assert)
        prop = "($(z.children[1].name) $child_prop)"
        
    else # an expression with operators and children
        child_props = map( (c) -> smt!(c, declarations, propositions, cache, depth+1, assert=assert) , z.children)
        prop = "($(__smt_opnames(z)) $(join(child_props, " ")))"

    end
    return prop
end


"""
    smt(z::AbstractExpr)
    smt(z1,...,zn; assert=true)
    smt([z1,...,zn]; assert=true, line_ending='\n', as_list=true)

Generate the SMT representation of `z` or `and(z1,...,zn)`.

When calling `smt([z1,...,zn])`, the array must have type `Array{AbstractExpr}`. Note that list comprehensions do not preserve array typing. For example, if `z` is an array of `BoolExpr`, `[z[i] for i=1:n]` will be an array of type `Any`. To preserve the correct type, use `BoolExpr[z[i] for i=1:n]`.

Optional keyword arguments are:
1. `assert = true|false`: default `true`. Whether to generate the (assert ...) SMT-LIB statement, which asserts that an expression must be true. This option is only valid if `smt` is called on a Boolean expression.
2. `line_ending`: If not set, this defaults to "\r\n" on Windows and '\n' everywhere else.
3. `as_list = true|false`: default `false`. When `true`, `smt` returns a list of commands instead of a single `line_ending`-separated string.
"""
function smt(zs_mixed::Vararg{Union{Array{T}, T}}; assert=true, line_ending=Sys.iswindows() ? "\r\n" : "\n", as_list=false) where T <: AbstractExpr
    declarations = String[]
    propositions = String[]
    cache = Dict{UInt64, String}()

    zs = cat(map((z) -> isa(z, Array) ? flatten(z) : [z], zs_mixed)..., dims=1)
    propositions = map((z) -> smt!(z, declarations, propositions, cache, 0, assert=assert), zs)
    
    # Returning 
    statements = assert ?
                 cat(declarations, map((i) -> "(assert $(propositions[i]))", filter( (i) -> isa(zs[i], BoolExpr), 1:length(propositions))), dims=1) :
                 cat(declarations, map((i) -> "(define-fun $(zs[i].name) () $( __smt_typestr(zs[i])) $(propositions[i]))", filter((i) -> !(zs[i].op in [:const, :identity]),  1:length(propositions))), dims=1)
    if as_list
        return statements
    else
        # this expression concatenates all the strings in row 1, then all the strings in row 2, etc.
        return join(statements, line_ending)*line_ending
    end
end


##### WRITE TO FILE #####

"""
    save(z1, z2,..., io=open("out.smt", "w"))
    save(z1, z2,..., io=open("out.smt", "w", line_ending='\n', start_commands=nothing, end_commands=nothing)

Write the SMT representation of `z` or `and(z1,...,zn)` to an IO object.
Keyword arguments:
* `io` is a Julia IO object, for example an open file for writing.
* `line_ending` configures the line ending character. If left off, the default is `\r\n` on Windows systems and `\n` everywhere else.
* `start_commands` are inserted before `smt(z)`. Typically one uses this to include `(set-info ...)` or `(set-option ...)` statements.
* `end_commands` are inserted after `(check-sat)`. This tends to be less useful unless you already know whether your problem is satisfiable.
"""
function save(zs::Vararg{Union{Array{T}, T}}; io=open("out.smt", "w"), assert=true, check_sat=true, line_ending=nothing, start_commands=nothing, end_commands=nothing) where T <: AbstractExpr
    if isnothing(line_ending)
        line_ending = Sys.iswindows() ? "\r\n" : '\n'
    end

    if assert && !all((isa.(zs, BoolExpr)) .| isa.(zs, Array{T} where T <: BoolExpr))
        @warn "Top-level expression must be Boolean to produce a valid SMT program."
    end
    if !isnothing(start_commands)
        write(io, start_commands*"$line_ending")
    end
    write(io, smt(zs..., assert=assert, line_ending=line_ending))
    if check_sat
        write(io, "(check-sat)$line_ending")
    end
    if !isnothing(end_commands)
        write(io, end_commands*"$line_ending")
    end
    close(io)
end
