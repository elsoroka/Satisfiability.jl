push!(LOAD_PATH, "../src")
using Satisfiability

# Is there a function `f(x)` such that `f(f(x)) == x`, `f(x) == y` and `x != y`?

@satvariable(x, Bool)
@satvariable(y, Bool)
@uninterpreted(f, Bool, Bool)

# When using Yices, you must set the logic. Here we set it to "QF_UFLIA" - "Quantifier free uninterpreted functions, linear integer arithmetic".
# (This is OK even though we're only using Boolean variables. We have to include uninterpreted functions or Yices will hang.)
status = sat!(distinct(x,y), f(x) == y, f(f(x)) == x, solver=Yices(), logic="QF_UFLIA")
println("status = $status")

# It turns out there is. Since the satisfying assignment for an uninterpreted function is itself a function,
# Satisfiability.jl represents this by setting the value of `f` to this function.
# Now calling `f(value)` will return the value of this satisfying assignment.
println(f(x.value) == y.value) # true
println(f(f(x.value)) == x.value) # true