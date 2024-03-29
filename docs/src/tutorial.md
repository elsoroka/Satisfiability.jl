# Tutorial
Here we present several mini-examples of SMT problems.
## Proving the validity of De Morgan's law
This example is borrowed from Microsoft's [introduction](https://microsoft.github.io/z3guide/docs/logic/propositional-logic/) to Z3 for propositional logic.

We say a formula is **valid** if it is true for every assignment of values to its variables. For example, `z ∨ ¬z` is valid. (This is useful because a valid formula can provide a useful transformation or simplification of a logical expression.)

One famous transformation is De Morgan's law: `a ∧ b = ¬(¬a ∨ ¬b)`. To show validity of De Morgan's law, we can construct the bidirectional implication `a ∧ b ⟺ ¬(¬a ∨ ¬b)`. It suffices to show that the negation of this formula is unsatisfiable.

```@example 1
using Satisfiability 
@satvariable(a, Bool)
@satvariable(b, Bool)

conjecture = iff(a ∧ b, ¬(¬a ∨ ¬b))
status = sat!(¬conjecture, solver=Z3()) # status will be either :SAT or :UNSAT
```

## A common logical mistake
Suppose you have Boolean variables `p`, `q` and `r`. A common mistake made by students in discrete math classes is to think that if `p` implies `q` and `q` implies `r` (`(p ⟹ q) ∧ (q ⟹ r)`) then `p` must imply `r` (`p ⟹ r`). Are these statements equivalent? We can use a SAT solver to check.

```@example 1
@satvariable(p, Bool)
@satvariable(q, Bool)
@satvariable(r, Bool)

conjecture = iff((p ⟹ q) ∧ (q ⟹ r), p ⟹ r)
status = sat!(¬conjecture, solver=Z3())
```
Unlike the previous example the status is `:SAT`, indicating there is an assignment `p`, `q` and `r` that disproves the conjecture.

```@example 1
println("p = $(value(p))")
println("q = $(value(q))")
println("r = $(value(r))")
```

## Optimizing over integers
The knapsack problem is a famous NP-complete problem in which you are packing a bag that cannot exceed some maximum weight. Given a set of items with known value and weight, you want to pack a subset that maximizes the value.

A simpler version, illustrated in this [classic XKCD strip](https://xkcd.com/287/), is to pack the bag to exactly its maximum weight (or spend a specific amount of money).
In fact, the problem in the XKCD strip can be expressed as a linear equation over integers.

```@example 1
@satvariable(a[1:6], Int)
c = [215; 275; 335; 355; 420; 580]
expr = and(and(a .>= 0), sum(a .* c) == 1505)
sat!(expr, solver=Z3())
println("Result: $(value(a))")
println("Check: $(sum(value(a) .* c))")
```

## Proving properties of fixed-size integer arithmetic
This example is from Microsoft's [Z3 tutorial](https://microsoft.github.io/z3guide/docs/theories/Bitvectors/).
A bitvector `x` is a power of two (or zero) if and only if `x & (x - 1)` is zero, where & is bitwise and. We prove this property for an 8-bit vector.

```@example 1
println("Example 1 (should be SAT)")
@satvariable(b, BitVector, 8)
is_power_of_two = b & (b - 0x01) == 0

# iff is_power_of_two holds, b must be one of 1, 2, 4, ... 128
expr = iff(is_power_of_two,
           or(b == 2^i for i=0:7))
status = sat!(expr, solver=Z3())
#println(smt(expr))
println(status) # if status is SAT we proved it.
```
