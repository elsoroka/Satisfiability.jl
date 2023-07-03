# [BooleanSatisfiability](https://elsoroka.github.io/BooleanSatisfiability.jl)

![example workflow](https://github.com/github/docs/actions/workflows/ci.yml/badge.svg) [![codecov](https://codecov.io/gh/elsoroka/BooleanSatisfiability.jl/branch/main/graph/badge.svg?token=84BIREQL46)](https://codecov.io/gh/elsoroka/BooleanSatisfiability.jl)

[![Build Status](https://github.com/elsoroka/BooleanSatisfiability.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/elsoroka/BooleanSatisfiability.jl/actions/workflows/CI.yml?query=branch%3Amain)

BooleanSatisfiability.jl is a package for representing Boolean satisfiability (SAT) and selected other satisfiability modulo theories (SMT) problems in Julia. This package provides a simple front-end interface to common SMT solvers, including full support for vector-valued and matrix-valued expressions.

* Easily specify single-valued or vector-valued Boolean SAT, integer or real-valued SMT problems using Julia's built-in broadcasting capabilities.
* Generate files in [SMT2](http://www.smtlib.org/) format.
* BooleanSatisfiability.jl calls [Z3](https://www.microsoft.com/en-us/research/publication/z3-an-efficient-smt-solver/) as the back-end solver and interprets the result.

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
