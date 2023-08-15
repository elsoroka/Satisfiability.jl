push!(LOAD_PATH, "../src")
push!(LOAD_PATH, "./")
using BooleanSatisfiability

# https://microsoft.github.io/z3guide/docs/theories/Bitvectors/
# There is a fast way to check that fixed size numbers are powers of two.
# A bitvector x is a power of two or zero if and only if x & (x - 1) is zero,
# where & represents the bitwise and. We check this for 8 bits.
println("Example 1 (should be SAT)")
@satvariable(b, BitVector, 8)
is_power_of_two = b & (b - 0x01) == 0

# iff is_power_of_two holds, b must be one of 1, 2, 4, ... 128
expr = iff(is_power_of_two,
           any([b == 2^i for i=0:7]))
status = sat!(expr)
#println(smt(expr))
println(status) # if status is SAT we proved it.


# Here is another mini example: a bitwise version of de Morgan's law.
# In this example we want to show there is NO possible value of x and y such that de Morgan's bitwise law doesn't hold.
println("Example 2 (should be UNSAT)")
@satvariable(x, BitVector, 64)
@satvariable(y, BitVector, 64)

expr = not((~x & ~y) == ~(x | y))
status = sat!(expr)
println(smt(expr))

println(status) # if status is UNSAT we proved it.
