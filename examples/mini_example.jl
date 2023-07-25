push!(LOAD_PATH,"../src/")
using BooleanSatisfiability

# let's define a matrix of Boolean statements
n = 3
m = 2
@satvariable(x[1:m, 1:n], Bool)
@satvariable(y[1:m, 1:n], Bool)
@satvariable(z[1:n], Bool)

# At each step, either x or y has to be true
expr1 = all(x .∨ y) .∨ and.(¬z, z)

# One z out of n has to be true
expr2 = any(z)

# I want both of these to be true (TODO fix this interface)
status = sat!(expr1, expr2, solver=Z3())
println("status = $status")
if status == :SAT
    println("x = $(value(x))")
    println("y = $(value(y))")
    println("z = $(value(z))")
else # x.value, y.value and z.value will be nothing
    println("Didn't find a solution.")
end