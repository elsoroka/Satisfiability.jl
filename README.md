# [Satisfiability.jl](https://elsoroka.github.io/Satisfiability.jl)

[![build status](https://github.com/elsoroka/Satisfiability.jl/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/elsoroka/Satisfiability.jl/actions/workflows/CI.yml?query=branch%3Amain) [![docs](https://github.com/elsoroka/Satisfiability.jl/actions/workflows/docs.yml/badge.svg)](https://elsoroka.github.io/Satisfiability.jl/) [![codecov](https://codecov.io/gh/elsoroka/BooleanSatisfiability.jl/branch/main/graph/badge.svg?token=84BIREQL46)](https://codecov.io/gh/elsoroka/BooleanSatisfiability.jl)

Satisfiability.jl is a package for representing satisfiability modulo theories (SMT) problems in Julia. This package provides a simple front-end interface to common SMT solvers, including full support for vector-valued and matrix-valued expressions. Currently, the theories of propositional logic, Integers, Reals and fixed-size BitVectors are supported. We will eventually add support for all [SMT-LIB standard theories](http://smtlib.cs.uiowa.edu/theories.shtml).

What you can do with this package:
* Easily specify single-valued or vector-valued SMT expressions using Julia's built-in broadcasting capabilities.
* Generate files in the [SMT-LIB](http://www.smtlib.org/) specification language.
* Interact with any solver that follows the SMT-LIB standard.

You can read the documentation [here](https://elsoroka.github.io/Satisfiability.jl/dev/).

## Examples

### Solving the vector-valued Boolean problem
(x1 ∧ y1) ∨ (¬x1 ∧ y1) ∧ ... ∧ (xn ∧ yn) ∨ (¬xn ∧ yn)
```
@satvariable(x[1:n], Bool)
@satvariable(y[1:n], Bool)
expr = (x .∧ y) .∨ (¬x .∧ y)
status = sat!(expr, solver=Z3())
println("x = $(value(x)), y = $(value(y))”)
```

### Investigating rounding of real numbers
This problem (from Microsoft's [Z3 tutorials](https://microsoft.github.io/z3guide/docs/theories/Arithmetic)) uses mixed integer and real variables to figure out whether there exists a constant `a` and two real numbers `xR` and `yR` such that `round(xR) +  round(yR)  > a` while `xR + yR < a`.
```
@satvariable(xR, Real)
@satvariable(yR, Real)
@satvariable(x, Int) # x represents a rounded version of xR
@satvariable(y, Int) # y represents a rounded version of yR
@satvariable(a, Int)

exprs = [xR + yR < a,
         x + y > a,
         or(x == xR, ((x < xR) ∧ (xR < x+1)), ((x-1 < xR) ∧ (xR < x))),
         or(y == yR, ((y < yR) ∧ (yR < y+1)), ((y-1 < yR) ∧ (yR < y))),
        ]
status = sat!(exprs)
println("status = $status, xR=$(value(xR)), yR=$(value(yR))")
```

### Proving a bitwise version of de Morgan's law.
In this example we want to show there is NO possible value of x and y such that de Morgan's bitwise law doesn't hold.
```
@satvariable(x, BitVector, 64)
@satvariable(y, BitVector, 64)

expr = not((~x & ~y) == ~(x | y))

status = sat!(expr, solver=Z3())
println(status) # if status is UNSAT we proved it.
```

## Development status
Working on a first release! Follow for updates.
