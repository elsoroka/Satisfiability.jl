# Tutorial
Here we present several mini-examples of SAT problems.
## Proving the validity of De Morgan's law
This example is borrowed from Microsoft's [introduction](https://microsoft.github.io/z3guide/docs/logic/propositional-logic/) to Z3 for propositional logic.

We say a formula is **valid** if it is true for every assignment of values to its variables. For example, `z ∨ ¬z` is valid. (This is useful because a valid formula can provide a useful transformation or simplification of a logical expression.)

One famous transformation is De Morgan's law: `a ∧ b = ¬(¬a ∨ ¬b)`. To show validity of De Morgan's law, we can construct the bidirectional implication `a ∧ b ⟺ ¬(¬a ∨ ¬b)`. It suffices to show that the negation of this formula is unsatisfiable.

```@example
a = Bool("a")
b = Bool("b")

conjecture = iff(a ∧ b, ¬(¬a ∨ ¬b))
status = sat!(¬conjecture) # status will be either :SAT or :UNSAT
```
## A common logical mistake
Suppose you have Boolean variables `p`, `q` and `r`. A common mistake made by students in discrete math classes is to think that if `p` implies `q` and `q` implies `r` (`(p ⟹ q) ∧ (q ⟹ r)`) then `p` must imply `r` (`p ⟹ r`). Are these statements equivalent? We can use a SAT solver to check.

```@example
p = Bool("p")
q = Bool("q")
r = Bool("r")

conjecture = iff((p ⟹ q) ∧ (q ⟹ r), p ⟹ r)
status = sat!(¬conjecture)
```
Unlike the previous example the status is `:SAT`, indicating there is an assignment `p`, `q` and `r` that disproves the conjecture.

```@example
println("p = $(value(p))")
println("q = $(value(q))")
println("r = $(value(r))")
```
