# SMT-LIB theories http://smtlib.cs.uiowa.edu/theories.shtml
__valid_vartypes = [:Bool, :Int, :Real, :BitVector, :FloatingPoint, :String, :Array]
"""
    @satvariable(z, Bool)
	@satvariable(a[1:n], Int)

Construct a SAT variable with name z, optional array dimensions, and specified type (`Bool`, `Int` or `Real`).

One and two-dimensional variables can be constructed with the following syntax.
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

	# inside here name and t are exprs
	if isa(expr, Symbol) # one variable, eg @Bool(x)
		name = string(expr)
		# this line resolves to something like x = Bool("x")
		# special handling of parametric BitVector
        if typename == :BitVector
           return esc(:($expr = $(typename)($(name),$(arrsize)))) 
        else
            return esc(:($expr = $(typename)($name)))
        end

	elseif length(expr.args) == 2 && isa(expr.args[1], Symbol)
		stem = expr.args[1]
		name = string(stem)
		iterable = expr.args[2]
        if typename == :BitVector
            return esc(:($stem = [$(typename)("$(:($$name))_$(i)",$(arrsize)) for i in $iterable]))
        else
		    return esc(:($stem = [$(typename)("$(:($$name))_$(i)") for i in $iterable]))
        end
	elseif length(expr.args) == 3
		stem = expr.args[1]
		name = string(stem)
		iterable1, iterable2 = expr.args[2], expr.args[3]
        if typename == :BitVector
            return esc(:($stem = [$(typename)("$(:($$name))_$(i)_$(j)",$(arrsize)) for i in $iterable1, j in $iterable2]))
        else
		    return esc(:($stem = [$(typename)("$(:($$name))_$(i)_$(j)") for i in $iterable1, j in $iterable2]))
        end
	else
		@error "Unable to create variable from expression $expr. Recommended usage: \"@satvariable(x, Bool)\", \"@satvariable(x[1:n], Int)\", or \"@satvariable(x[1:m, 1:n], Bool)\"."
	end
end
