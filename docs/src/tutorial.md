# Tutorial
Here we present several mini-examples of SMT problems.
## Proving the validity of De Morgan's law
This example is borrowed from Microsoft's [introduction](https://microsoft.github.io/z3guide/docs/logic/propositional-logic/) to `Z3` for propositional logic.

We say a formula is **valid** if it is true for every assignment of values to its variables. For example, `z ∨ ¬z` is valid. (This is useful because a valid formula can provide a useful transformation or simplification of a logical expression.)

One famous transformation is De Morgan's law: `a ∧ b = ¬(¬a ∨ ¬b)`. To show validity of De Morgan's law, we can construct the bidirectional implication `a ∧ b ⟺ ¬(¬a ∨ ¬b)`. It suffices to show that the negation of this formula is unsatisfiable.

```jldoctest; output = false
using Satisfiability 
@satvariable(a, Bool)
@satvariable(b, Bool)

conjecture = iff(a ∧ b, ¬(¬a ∨ ¬b))
status = sat!(¬conjecture, solver=Z3()) # status should be :UNSAT

# output

:UNSAT
```

## Implications
Suppose you have Boolean variables `p`, `q` and `r`. We want to find out: if `p` implies `q` and `q` implies `r` (`(p ⟹ q) ∧ (q ⟹ r)`) will `p` imply `r` (`p ⟹ r`)? We can use a SAT solver to check.

```jldoctest label9; output = false
using Satisfiability
@satvariable(p, Bool)
@satvariable(q, Bool)
@satvariable(r, Bool)

conjecture = ((p ⟹ q) ∧ (q ⟹ r)) ⟹ (p ⟹ r)
status = sat!(¬conjecture, solver=Z3())

# output

:UNSAT
```
Since the status is UNSAT, there is no example that disproves the conjecture. We see that the variables have taken on the value `nothing`.


```jldoctest label9; output = false
println("p = $(value(p))")
println("q = $(value(q))")
println("r = $(value(r))")

# output

p = nothing
q = nothing
r = nothing
```

## Optimizing over integers
The knapsack problem is a famous NP-complete problem in which you are packing a bag that cannot exceed some maximum weight. Given a set of items with known value and weight, you want to pack a subset that maximizes the value.

A simpler version, illustrated in this [classic XKCD strip](https://xkcd.com/287/), is to pack the bag to exactly its maximum weight (or spend a specific amount of money).
In fact, the problem in the XKCD strip can be expressed as a linear equation over integers.

```jldoctest; output = false 
using Satisfiability
@satvariable(a[1:6], Int)
c = [215; 275; 335; 355; 420; 580]

expr = and(and(a .>= 0), sum(a .* c) == 1505)
sat!(expr, solver=Z3())

println("Result: $(value(a))")
println("Check: $(sum(value(a) .* c))")

# output

Result: [7, 0, 0, 0, 0, 0]
Check: 1505
```

## Proving properties of fixed-size integer arithmetic
This example is from Microsoft's [Z3 tutorial](https://microsoft.github.io/z3guide/docs/theories/Bitvectors/).
A Bitvector `x` is a power of two (or zero) if and only if `x & (x - 1)` is zero, where & is bitwise and. We prove this property for an 8-bit vector.

```jldoctest; output = false
using Satisfiability

@satvariable(b, BitVector, 8)
is_power_of_two = b & (b - 0x01) == 0

# iff is_power_of_two holds, b must be one of 1, 2, 4, ... 128
expr = iff(is_power_of_two,
           or(b == 2^i for i=0:7))
status = sat!(expr, solver=Z3())
println(status) # if status is SAT we proved it.

# output

SAT
```
