##### CALLING A SAT SOLVER #####

include("call_solver.jl")

"""
    solver = Z3()
    sat!(z::BoolExpr, solver)
    sat!(z1, z2,..., solver)
    
Solve the SAT problem using a Solver. If the problem is satisfiable, update the values of all `BoolExprs` in `prob` with their satisfying assignments.

Possible return values are `:SAT`, `:UNSAT`, or `:ERROR`. `prob` is only modified to add Boolean values if the return value is `:SAT`.
"""
function sat!(prob::BoolExpr, solver::Solver, clear_values_if_unsat=true)

    smt_problem = smt(prob)*"(check-sat)\n"
    status, values, proc = talk_to_solver(smt_problem, solver)
    
    # Only assign values if there are values. If status is :UNSAT or :ERROR, values will be an empty dict.
    if status == :SAT
        __assign!(prob, values)
    elseif clear_values_if_unsat
        __clear_assignment!(prob)
    end
    # TODO we don't need it rn, we return it in case we do useful things with it later like requesting unsat cores and stuff
    kill(proc)
    return status
end

sat!(zs::Vararg{Union{Array{T}, T}}; solver=Z3()) where T <: BoolExpr = length(zs) > 0 ?
                                                           sat!(__flatten_nested_exprs(all, zs...), solver) :
                                                           error("Cannot solve empty problem (no expressions).")

                                                           # this version accepts an array of exprs and [exprs] (arrays), for example sat!([z1, z2, z3])
sat!(zs::Array, solver::Solver) = sat!(zs...; solver=Solver)


##### ASSIGNMENTS ####
# see discussion on why this is the way it is
# https://docs.julialang.org/en/v1/manual/performance-tips/#The-dangers-of-abusing-multiple-dispatch-(aka,-more-on-types-with-values-as-parameters)
# https://groups.google.com/forum/#!msg/julia-users/jUMu9A3QKQQ/qjgVWr7vAwAJ
__reductions = Dict(
    :not     => (values) -> !(values[1]),
    :and     => (values) -> reduce(&, values),
    :or      => (values) -> reduce(|, values),
    :xor     => (values) -> sum(values) == 1,
    :implies => (values) -> !(values[1]) | values[2],
    :iff     => (values) -> values[1] == values[2],
    :ite     => (values) -> (values[1] & values[2]) | (values[1] & values[3]),
    :eq      => (values) -> values[1] == values[2],
    :lt      => (values) -> values[1] < values[2],
    :leq     => (values) -> values[1] <= values[2],
    :gt      => (values) -> values[1] > values[2],
    :geq     => (values) -> values[1] >= values[2],
    :add     => (values) -> sum(values),
    :sub     => (values) -> values[1] - sum(values[2:end]) ,
    :mul     => (values) -> prod(values),
    :div     => (values) -> values[1] / prod(values[2:end]),
)

function __assign!(z::T, values::Dict) where T <: AbstractExpr
    if z.op == :identity
        if z.name ∈ keys(values)
            z.value = values[z.name]
        else
            z.value = missing # this is better than nothing because & and | automatically skip it (three-valued logic).
        end
    elseif z.op == :const
        ; # const already has .value set so do nothing
    else
        map( (z) -> __assign!(z, values), z.children)
        values = getproperty.(z.children, :value)
        if z.op ∈ keys(__reductions)
            z.value = __reductions[z.op](values)
        else
            @error("Unknown operator $(z.op)")
        end
    end
end

function __clear_assignment!(z::AbstractExpr)
    z.value = nothing
    if length(z.children) > 0
        map(__clear_assignment!, z.children)
    end
end