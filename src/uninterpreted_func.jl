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

mutable struct UninterpretedFunc <: AbstractExpr
    op       :: Symbol
    children :: Array{AbstractExpr}
    value    :: Union{Function, Nothing, Missing}
    name     :: String
    __is_commutative :: Bool
    call_on_vars::Union{Function, Nothing}
    call_on_const::Union{Function, Nothing}

    UninterpretedFunc(name::String) = new(:ufunc, AbstractExpr[], nothing, name, false, nothing, nothing)
end
# This enables the syntax f(x) on variables and constants.
(f::UninterpretedFunc)(x::T) where T <: AbstractExpr = begin
    e = f.call_on_vars(x)
    if !(isnothing(f.value) || ismissing(f.value))
        e.value = ismissing(x.value) || isnothing(x.value) ? x.value : f(x.value)
    end
    return e
end
(f::UninterpretedFunc)(x::C) where C = !(isnothing(f.value) || ismissing(f.value)) ? f.value(x) : f.call_on_const(x)

# this is for propagating values, which uses the name of the operation as the function call
ufunc(f::UninterpretedFunc, x::AbstractExpr) = f.value

"""
    @uninterpreted(f, Int, Bool) # f takes as input IntExpr and returns BoolExpr
    @uninterpreted(g, (BitVector, 32), (BitVector, 32)) # g's input and output values are BitVectors of length 32

Define an SMT-LIB uninterpreted function. An uninterpreted function can be thought of as an unknown mapping between input and output values.
The task of the SMT solver is then to determine whether a mapping exists such that some Boolean statement is true.

For example, we can ask whether there exists a function `f(x)`` such that `f(f(x)) == x`, `f(x) == y` and `x != y`.

```julia
@satvariable(x, Bool)
@satvariable(y, Bool)
@uninterpreted(f, Bool, Bool)

status = sat!(distinct(x,y), f(x) == y, f(f(x)) == x, solver=Z3())
println("status = \$status")
```
"""
macro uninterpreted_func(f, InTypespec, OutTypespec)
        # it must be BitVector with size
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

        if isa(OutType, Expr)
            return esc(
            quote
            $f = UninterpretedFunc("$($(String(f)))")
            # this is the function on its type
            $f.call_on_vars = (x::$InType) -> $OutType(:ufunc, AbstractExpr[$f, x], nothing, "$($(String(f)))_$(x.name)", x.length)
            # this is the function on its const type
            $f.call_on_const = (x::$ConstType) -> begin wx = $wrapper(x); $OutType(:ufunc, AbstractExpr[$f, wx], nothing, "$($(String(f)))_$(wx.name)", x.length) end
            end)
        else
            return esc(quote
            $f = UninterpretedFunc("$($(String(f)))")
            $f.call_on_vars = (x::$InType) -> $OutType(:ufunc, AbstractExpr[$f, x], nothing, "$($(String(f)))_$(x.name)")
            $f.call_on_const = (x::$ConstType) -> begin wx = $wrapper(x); $OutType(:ufunc, AbstractExpr[$f, wx], nothing, "$($(String(f)))_$(wx.name)") end
        end)
    end
end