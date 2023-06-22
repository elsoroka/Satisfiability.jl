##### CALLING A SAT SOLVER #####

include("call_solver.jl")

"""
    sat!(z::BoolExpr)
    sat!(z1, z2,...)
    
Solve the SAT problem using Z3. If the problem is satisfiable, update the values of all `BoolExprs` in `prob` with their satisfying assignments.

Possible return values are `:SAT`, `:UNSAT`, or `:ERROR`. `prob` is only modified to add Boolean values if the return value is `:SAT`.
"""
function sat!(prob::BoolExpr)
    smt_problem = smt(prob)*"(check-sat)\n"
    status, values, proc = talk_to_solver(smt_problem)
    # Only assign values if there are values. If status is :UNSAT or :ERROR, values will be an empty dict.
    if status == :SAT
        __assign!(prob, values)
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