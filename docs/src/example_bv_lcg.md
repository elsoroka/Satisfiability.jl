# Predicting the output of a tiny LCG
This example is "3.10.1 Cracking LCG with Z3" from *[SAT/SMT by Example](https://sat-smt.codes/SAT_SMT_by_example.pdf)* by Dennis Yurichev.

A linear congruential generator (LCG) is an algorithm for generating pseudo-random numbers in which a series of transformations is used to move from one number to the next. LCGs are easy to implement using low-level bit operations, making them popular for resource-constrained embedded applications. However, they are unsuitable for many applications because their output is predictable.

*SAT/SMT by Example*, example 3.10.1 shows how to predict the future output of an LCG by encoding its transformations. The original example starts with a small C program that prints the output of `rand() % 100` 10 times, producing 10 2 digit random numbers. It turns out C's rand() has this LCG implementation:

1. `state = state * 214013 + 2531011`
2. `state = (state >> 16) & 0x7FFF`
3. `return state`

Suppose we observe 10 states `n1,...,n10 = [37, 29, 74, 95, 98, 40, 23, 58, 61, 17]` from the LCG. We want to predict `n0`, the number before `n1`, and `n11`, the number after `n10`. (These are the numbers from *SAT/SMT by Example*.)

```@example
using BooleanSatisfiability

@satvariable(states[1:10], BitVector, 32)
@satvariable(output_prev, BitVector, 32)
@satvariable(output_next, BitVector, 32)
```
```@example
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
```
```@example
expr = and(all(transitions), all(remainders))
status = sat!(expr, solver=CVC5())
println("status = $status")

for (i,state) in enumerate(states)
    println("state $i = $(value(state))")
end

# According to SAT/SMT By Example the previous output is 37 and the next output is 17.
println("prev = $(value(output_prev))")
println("next = $(value(output_next))")
```
