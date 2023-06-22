# Solving Boolean SAT Problems in Julia
BooleanSatisfiability.jl is a package for representing Boolean satisfiability (SAT) problems in Julia. This package provides a simple front-end interface to common SAT solvers with full support for vector-valued and matrix-valued Boolean expressions.

```@contents
Pages = ["index.md"]
Depth = 4
```

## What is a SAT problem?
### Boolean variables and literals
A Boolean variable can only take on the values `true` or `false` (0 or 1).

The variable `z`, which could be either `true` or `false`, is a **variable**, while the value `true` is a **literal**. Julia provides built-in support for Boolean literals using the `Bool` type. This package defines the BoolExpr type to represent Boolean variables.

### Logical formulae
We can construct a logical formula using Boolean variables, literals, and operators. This package defines four operators. Both the plaintext and mathematical symbols are available.

* `not(z)`, or `¬z`: the negation of `z`.
* `and(z1, z2)` or `z1 ∧ z2`. The n-ary version, `and(z1,...,zn)`, is also available.
* `and(z1, z2)` or `z1 ∨ z2`. The n-ary version, `and(z1,...,zn)`, is also available.
* `implies(z1, z2)` or `z1 ⟹ z2`.

These expressions can be nested to produce formulae of arbitrary complexity.

### SAT problems
Given a Boolean expression, the associated SAT problem can be posed as:

**"Is there a satisfying assignment of literals (1's and 0's) such that this formula is true?"**

* If this assignment exists, we say the formula is **satisfiable**. More than one satisfying assignment may exist for a given formula.

* If the assignment does not exist, we say the formula is **unsatisfiable**.

## How does BooleanSatisfiability.jl work?
BooleanSatisfiability.jl provides an **interface** to SAT solvers that accept input in the [SMTLIB2](http://www.smtlib.org/) format. It works by generating the SMT representation of your problem, then invoking a solver to read said file.

Currently, [Z3](https://microsoft.github.io/z3guide/) is supported.