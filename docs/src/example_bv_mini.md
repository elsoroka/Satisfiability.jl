# BitVectors

BitVectors represent arrays of binary values. Because they model how data is represented in a computer, they can be used to prove properties of computer systems.

These two mini-examples are taken from [Microsoft's Z3 documentation](https://microsoft.github.io/z3guide/docs/theories/Bitvectors/).

First, we want to prove the statement "a BitVector x is a power of two or zero if and only if x & (x - 1) is zero", where & represents bitwise and.

This is useful because it provides a fast way to check that fixed size numbers are powers of two. We'll check the property for 8 bits.

```jldoctest label7; output = false
using Satisfiability

println("Example 1 (should be SAT)")
@satvariable(b, BitVector, 8)
is_power_of_two = b & (b - 0x01) == 0

# iff is_power_of_two holds, b must be one of 1, 2, 4, ... 128
expr = iff(is_power_of_two,
           or([b == 2^i for i=0:7]))
status = sat!(expr)
println(status) # if status is SAT we proved it.

# output

Example 1 (should be SAT)
SAT
```

Next, we can prove a bitwise version of de Morgan's law.
We want to show there is NO possible value of x and y such that de Morgan's bitwise law doesn't hold.

```jldoctest label7; output = false
println("Example 2 (should be UNSAT)")
@satvariable(x, BitVector, 64)
@satvariable(y, BitVector, 64)

expr = not((~x & ~y) == ~(x | y))

status = sat!(expr, solver=Z3())
println(status) # if status is UNSAT we proved it.

# output

Example 2 (should be UNSAT)
UNSAT
```