#=
Uninterpreted functions are SMT-LIB objects that take input of a specific type and give output of a specific type
In Julia, this looks like
@satvariable(f, UninterpretedFunc, Int, Int)
@satvariable(f, UninterpretedFunc, (BitVector, 32), (BitVector, 32))
@satvariable(f, UninterpretedFunc, (BitVector, 32), Bool)
etc
f(x) should return the right type expr with operator :name because the SMT syntax is (f x) for f(x)
thus, we only need to make sure the uninterpreted func is declared
and that (f x) works

=#

macro uninterpreted_func(f, InTypespec, OutTypespec)
        # it must be BitVector with size
        show(InTypespec)
        local wrapper = nothing
        local ConstType = nothing
        if isa(InTypespec, Expr) && InTypespec.args[1] == :BitVector
             # typeof(e).parameters[1] returns the type of the first parameter to the parametric type of e
            ConstType = nextsize(InTypespec.args[2])
            wrapper = (x) -> bvconst(x, bitcount(x)) # this is safe because a const of smaller bit-length can be combined with a variable of larger bit-length
        elseif InTypespec == :Int
            ConstType = Int
            wrapper = Satisfiability.__wrap_const
        elseif InTypespec == :Real
            ConstType = Float64
            wrapper = Satisfiability.__wrap_const
        elseif InTypespec == :Bool
            ConstType = Bool
            wrapper = (b) -> BoolExpr(:const, AbstractExpr[], b, "const_$b")
        else
            @error("Unable to determine wrapper function for $InTypespec-interoperable const")
        end
        
        local InType =  isa(InTypespec, Symbol) ?  Symbol("$(InTypespec)Expr") :  Expr(:curly, Symbol("$(InTypespec.args[1])Expr"), nextsize(InTypespec.args[2]))
        local OutType = isa(OutTypespec, Symbol) ? Symbol("$(OutTypespec)Expr") : Expr(:curly, Symbol("$(OutTypespec.args[1])Expr"), nextsize(OutTypespec.args[2]))

        return esc(quote
            # this is the function on its type
            $f(x::$InType) = $OutType(:ufunc, [x], nothing, "$(Satisfiability.__get_hash_name(Symbol($f), [x,]))")
            # this is the function on its const type
            $f(x::$ConstType) = begin wx = $wrapper(x); $OutType(:ufunc, AbstractExpr[wx,], nothing, "$(Satisfiability.__get_hash_name(Symbol($f), [wx,]))") end
        end)
end