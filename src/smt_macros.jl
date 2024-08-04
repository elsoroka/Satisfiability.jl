# SMT-LIB theories http://smtlib.cs.uiowa.edu/theories.shtml
__valid_vartypes = [:Bool, :Int, :Real, :BitVector, :FloatingPoint, :String, :Array]

"""
    @satvariable(z, Bool)
	@satvariable(a[1:n], Int)
	@satvariable(b, BitVector, 32)

Construct a SAT variable with name z, optional array dimensions, and specified type (`Bool`, `Int`, `Real` or `BitVector`).
Note that some  require an optional third parameter.

One and two-dimensional arrays of variables can be constructed with the following syntax. The result will be a native Julia array.
```julia
@satvariable(a[1:n], Int) # an Int vector of length n
@satvariable(x[1:m, 1:n], Real) # an m x n Int matrix
```
"""
macro satvariable(expr, typename, arrsize=1)
	# check typename
	if !isa(typename, Symbol) || !(typename ∈ __valid_vartypes) # unknown
		@error "Unknown expression type $typename"
	end
	# append Expr to typename
	typename = Symbol(typename, "Expr")

	# inside here name and t are exprs
	if isa(expr, Symbol) # one variable, eg @Bool(x)
		name = string(expr)
		# this line resolves to something like x = Bool("x")
		# special handling of parametric BitVector
        if typename == :BitVectorExpr
           return esc(:($expr = $(typename)($(name),$(arrsize)))) 
        else
            return esc(:($expr = $(typename)($name)))
        end
	elseif length(expr.args) == 2 && isa(expr.args[1], Symbol)
		stem = expr.args[1]
		name = string(stem)
		iterable = expr.args[2]
        if typename == :BitVectorExpr
            return esc(:($stem = [$(typename)("$(:($$name))_$(i)",$(arrsize)) for i in $iterable]))
        else
		    return esc(:($stem = [$(typename)("$(:($$name))_$(i)") for i in $iterable]))
        end
	elseif length(expr.args) == 3
		stem = expr.args[1]
		name = string(stem)
		iterable1, iterable2 = expr.args[2], expr.args[3]
        if typename == :BitVectorExpr
            return esc(:($stem = [$(typename)("$(:($$name))_$(i)_$(j)",$(arrsize)) for i in $iterable1, j in $iterable2]))
        else
		    return esc(:($stem = [$(typename)("$(:($$name))_$(i)_$(j)") for i in $iterable1, j in $iterable2]))
        end
	elseif length(expr.args) == 4
		stem = expr.args[1]
		name = string(stem)
		iterable1, iterable2, iterable3 = expr.args[2], expr.args[3], expr.args[4]
		if typename == :BitVectorExpr
			return esc(:($stem = [$(typename)("$(:($$name))_$(i)_$(j)_$(k)",$(arrsize)) for i in $iterable1, j in $iterable2, k in $iterable3]))
		else
		    return esc(:($stem = [$(typename)("$(:($$name))_$(i)_$(j)_$(k)") for i in $iterable1, j in $iterable2, k in $iterable3]))
		end
	else
		@error "Unable to create variable from expression $expr. Recommended usage: \"@satvariable(x, Bool)\", \"@satvariable(x[1:n], Int)\", or \"@satvariable(x[1:m, 1:n], Bool)\"."
	end
end
