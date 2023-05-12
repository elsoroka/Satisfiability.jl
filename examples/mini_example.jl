using BooleanSatisfiability

# let's define a matrix of Boolean statements
n = 2
m = 1

x = Bool(m, n, "x")
y = Bool(m, n, "y")
z = Bool(1, n, "z")

# At each step, either x or y has to be true
expr1 = x .∨ y

# One z out of n has to be true
expr2 = any(z)

# I want both of these to be true (TODO fix this interface)
prob = (expr1 .∧ expr2)
println(smt(prob))
println("(check-sat)")