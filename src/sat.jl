##### CALLING A SAT SOLVER #####

include("call_solver.jl")

"""
    sat!(z::BoolExpr)
    sat!(z1, z2,...)
    
Solve the SAT problem using Z3. If the problem is satisfiable, update the values of all `BoolExprs` in `prob` with their satisfying assignments.

Possible return values are `:SAT`, `:UNSAT`, or `:ERROR`. `prob` is only modified to add Boolean values if the return value is `:SAT`.
"""
function sat!(prob::BoolExpr; solver=:Z3, clear_values_if_unsat=true, custom_command="")
    cmd = custom_command == "" ? DEFAULT_SOLVER_CMDS[solver] : custom_command

    smt_problem = smt(prob)*"(check-sat)\n"
    status, values, proc = talk_to_solver(smt_problem, cmd)
    
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

sat!(zs::Vararg{Union{Array{T}, T}}) where T <: BoolExpr = length(zs) > 0 ?
                                                           sat!(__flatten_nested_exprs(all, zs...)) :
                                                           error("Cannot solve empty problem (no expressions).")

                                                           # this version accepts an array of exprs and [exprs] (arrays), for example sat!([z1, z2, z3])
sat!(zs::Array) = sat!(zs...)


##### ASSIGNMENTS ####
# see discussion on why this is the way it is
# https://docs.julialang.org/en/v1/manual/performance-tips/#The-dangers-of-abusing-multiple-dispatch-(aka,-more-on-types-with-values-as-parameters)
# https://groups.google.com/forum/#!msg/julia-users/jUMu9A3QKQQ/qjgVWr7vAwAJ
__reductions = Dict(
    :NOT     => (values) -> !(values[1]),
    :AND     => (values) -> reduce(&, values),
    :OR      => (values) -> reduce(|, values),
    :XOR     => (values) -> reduce(xor, values),
    :IMPLIES => (values) -> (values[1]) | values[2],
    :IFF     => (values) -> values[1] == values[2],
    :ITE     => (values) -> (values[1] & values[2]) | (values[1] & values[3]),
    :EQ      => (values) -> values[1] == values[2],
    :LT      => (values) -> values[1] < values[2],
    :LEQ     => (values) -> values[1] <= values[2],
    :GT      => (values) -> values[1] > values[2],
    :GEQ     => (values) -> values[1] >= values[2],
    :ADD     => (values) -> sum(values),
    :SUB     => (values) -> value[1] - sum(values[2:end]) 
    :MUL     => (values) -> prod(values)
    :DIV     => (values) -> value[1] / prod(values[2:end])
)

function __assign!(z::T, values::Dict) where T <: AbstractExpr
    if z.op == :IDENTITY
        if z.name ∈ keys(values)
            z.value = values[z.name]
        else
            z.value = missing # this is better than nothing because & and | automatically skip it (three-valued logic).
        end
    elseif z.op == :CONST
        ; # CONST already has .value set so do nothing
    else
        map( (z) -> __assign!(z, values), z.children)
        values = map( (z) -> z.value, z.children)
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