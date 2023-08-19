push!(LOAD_PATH, "../../src/")
push!(LOAD_PATH, "src/")
using Satisfiability
include("../../src/utilities.jl")

name = "out.smt"
file = readlines(open(name, "r")) # now they are lines
statements = map((a) -> __split_statements(a)[1], file) # now we get rid of the outer parentheses

# let's sort the lines
decls = filter((l) -> startswith(l, "declare-fun"), statements)
asserts = filter((l) -> startswith(l, "assert"), statements)

# some hacks to handle only two things
# declare-fun name () Sort
d = Dict{String, AbstractExpr}()

for decl in decls
    tmp = split(decl, " ", limit=4)
    varname = String(tmp[2]); type = String(tmp[4])

    if startswith(varname, "(") # extra parameter, like declare-fun varname (_ BitVec n)
        type, extra = split(__split_statements(varname)[1], " ")[2:3]
        sz = parse(Int, extra)
        eval(:(d[$varname] = Satisfiability.$(Symbol("$(type)Expr"))($varname, $sz)))
    else
        eval(:(d[$varname] = Satisfiability.$(Symbol("$(type)Expr"))($varname)))
    end
end

op_keys = Dict(
    "=" => (==),
)

function construct_expr(string_expr::String)
    op, vars... = split(string_expr, " ")
    map((var) -> startswith(var, "(") ? construct_expr(__split_statements(var)[1]) : d[var], vars)
    op = op ∈ keys(op_keys) ? op_keys[op] : eval(Symbol(op))
    return op(vars...)
end

exprs = construct_expr.(asserts)
println(exprs)