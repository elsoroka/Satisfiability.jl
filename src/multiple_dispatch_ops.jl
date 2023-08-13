# This allows and() to be used in multiple theories
# in a context-dependent manner

and(es_mixed::Array{T}) where T = __multidispatch_op(and, es_mixed)
or(es_mixed::Array{T}) where T  = __multidispatch_op(or, es_mixed)

function __multidispatch_op(op::Function, es_mixed::Array{T}) where T
    zs, literals = __check_inputs_nary_op(es_mixed, const_type=Bool, expr_type=BoolExpr)
    if !isnothing(zs) # successfully found the type
        return op(zs, literals)
    end
    zs, literals = __check_inputs_nary_op(es_mixed, const_type=Integer, expr_type=BitVectorExpr)
    if !isnothing(zs)
        return op(zs, literals)
    end
    @error("Unable to operate on mixed type inputs $es_mixed")
end