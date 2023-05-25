using BooleanSatisfiability

# let's define a matrix of Boolean statements
n = 3
m = 2

x = Bool(m, n, "x")
y = Bool(m, n, "y")
z = Bool(1, n, "z")

# At each step, either x or y has to be true
expr1 = and(x .∨ y)

# One z out of n has to be true
expr2 = any(z)

# I want both of these to be true (TODO fix this interface)
status = sat!(expr1, expr2)
println("status = $status")
if status == :SAT
    println("x = $(value(x))")
    println("y = $(value(y))")
    println("z = $(value(z))")
else # x.value, y.value and z.value will be nothing
    println("Didn't find a solution.")
end