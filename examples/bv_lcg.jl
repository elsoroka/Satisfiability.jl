# This example is from "SAT/SMT by Example" by Dennis Yurichev. It is example 3.10.1 Cracking LCG with Z3.
# A linear congruential generator (LCG) is an algorithm for generating pseudo-random numbers. A series of transformations is used to move from one number to the next
# LCGs are simple to implement using low-level bit operations. In SAT/SMT by example,
# Mr. Yurichev dumps the assmbly code for a small loop that prints `rand() % 100` (in C) 10 times.
# He finds the following LCG code:

# 1. `tmp := state * 214013 + 2531011`
# 2. `state = tmp`
# 3. `(state >> 16) & 0x7FFF`
# 4. `return state`

# Now suppose we observe 10 states n1,...,n10 = [37, 29, 74, 95, 98, 40, 23, 58, 61, 17] from the LCG.
# We want to predict n0, the number before n1, and n11, the number after n10.
# The following code does exactly that.
using Satisfiability

@satvariable(states[1:10], BitVector, 32)
@satvariable(output_prev, BitVector, 32)
@satvariable(output_next, BitVector, 32)

transitions = BoolExpr[states[i+1] == states[i] * 214013+2531011 for i=1:9]
remainders = BoolExpr[
    output_prev == urem(( states[1] >> 16 ) & 0x7FFF, 100),
    urem(( states[2] >> 16) & 0x7FFF, 100) == 29,
    urem(( states[3] >> 16) & 0x7FFF, 100) == 74,
    urem(( states[4] >> 16) & 0x7FFF, 100) == 95,
    urem(( states[5] >> 16) & 0x7FFF, 100) == 98,
    urem(( states[6] >> 16) & 0x7FFF, 100) == 40,
    urem(( states[7] >> 16) & 0x7FFF, 100) == 23,
    urem(( states[8] >> 16) & 0x7FFF, 100) == 58,
    urem(( states[9] >> 16) & 0x7FFF, 100) == 61,
    output_next == urem(( states[10] >> 16) & 0x7FFF, 100),
]

expr = and(all(transitions), all(remainders))
status = sat!(expr, solver=CVC5())
println("status = $status")

for (i,state) in enumerate(states)
    println("state $i = $(value(state))")
end
println("prev = $(value(output_prev))")
println("next = $(value(output_next))")

# According to Mr. Yurichev's example, the previous output is 37 and the next output is 17!
# This matches on my machine using Z3 and CVC5.
