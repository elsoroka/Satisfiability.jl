# BooleanSatisfiability
![example workflow](https://github.com/github/docs/actions/workflows/test.yml/badge.svg) [![codecov](https://codecov.io/gh/elsoroka/BooleanSatisfiability.jl/branch/main/graph/badge.svg?token=84BIREQL46)](https://codecov.io/gh/elsoroka/BooleanSatisfiability.jl)

[![Build Status](https://github.com/elsoroka/BooleanSatisfiability.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/elsoroka/BooleanSatisfiability.jl/actions/workflows/CI.yml?query=branch%3Amain)

A package for solving Boolean satisfiability problems in Julia.

* Easily specify single-valued or vector-valued Boolean SAT problems using Julia's built-in broadcasting capabilities.
* Generate files in SMTLIB2 format.
* Uses [Z3](https://www.microsoft.com/en-us/research/publication/z3-an-efficient-smt-solver/) as the back-end solver.

## Example

Solving the single-valued problem **(x ∧ y) ∨ (¬x ∧ y)**
```
x = Bool("x")
y = Bool("y")
expr = (x ∧ y) ∨ (¬x ∧ y)
status = sat!(expr)
println("x = $(value(x)), y = $(value(y))”)
```

Solving the vector-valued problem **(x1 ∧ y1) ∨ (¬x1 ∧ y1) ∧ ... ∧ (xn ∧ yn) ∨ (¬xn ∧ yn)**
```
x = Bool(n, "x")
y = Bool(n, "y")
expr = (x .∧ y) .∨ (¬x .∧ y)
status = sat!(expr)
println("x = $(value(x)), y = $(value(y))”)
```

## Development status
Working on a first release! Follow for updates.