# Uninterpreted Functions


An uninterpreted function is a function where the mapping between input and output is not known. The task of the SMT solver is then to determine a mapping such that some SMT expression holds true.

Satisfiability.jl represents uninterpreted functions as callable structs. This enables the simple syntax:
```julia
@uninterpreted(myfunc, Int, Int)

# we can call myfunc on an Int constant or variable
@satvariable(a, Int)
myfunc(a)
myfunc(-2) # returns 

# we cannot call myfunc on the wrong type
# myfunc(true) yields an error
# myfunc(1.5) yields an error
```

As a small example, we can ask whether there exists a function `f(x)` such that `f(f(x)) == x`, `f(x) == y` and `x != y`.

```julia
@satvariable(x, Bool)
@satvariable(y, Bool)
@uninterpreted(f, Bool, Bool)

status = sat!(distinct(x,y), f(x) == y, f(f(x)) == x, solver=Z3())
println("status = \$status")
```

It turns out there is. Since the satisfying assignment for an uninterpreted function is itself a function, Satisfiability.jl represents this by setting the value of `f` to this function. Now calling `f(value)` will return the value of this satisfying assignment.

```julia
println(f(x.value)) # prints 0
println(f(x.value) == y.value) # true
println(f(f(x.value)) == x.value) # true
```