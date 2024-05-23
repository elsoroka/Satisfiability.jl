# [Satisfiability.jl](https://elsoroka.github.io/Satisfiability.jl)

[![build status](https://github.com/elsoroka/Satisfiability.jl/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/elsoroka/Satisfiability.jl/actions/workflows/CI.yml?query=branch%3Amain) [![docs](https://github.com/elsoroka/Satisfiability.jl/actions/workflows/docs.yml/badge.svg)](https://elsoroka.github.io/Satisfiability.jl/) [![codecov](https://codecov.io/gh/elsoroka/Satisfiability.jl/branch/main/graph/badge.svg?token=84BIREQL46)](https://codecov.io/gh/elsoroka/Satisfiability.jl)

Satisfiability.jl is a package for representing satisfiability modulo theories (SMT) problems in Julia. This package provides a simple front-end interface to common SMT solvers, including full support for vector-valued and matrix-valued expressions. Currently, the theories of propositional logic, uninterpreted functions, Integers, Reals and fixed-size BitVectors are supported. We will eventually add support for all [SMT-LIB standard theories](http://smtlib.cs.uiowa.edu/theories.shtml).

What you can do with this package:
* Cleanly specify SMT expressions using Julia's built-in broadcasting and iteration capabilities to write concise expressions.
* Generate files in the [SMT-LIB](http://www.smtlib.org/) specification language.
* Interact with any solver that follows the SMT-LIB standard. We test with Z3, CVC5, and Yices.

You can read the documentation [here](https://elsoroka.github.io/Satisfiability.jl/).

## Examples

### Solving the vector-valued Boolean problem
(x1 ∧ y1) ∨ (¬x1 ∧ y1) ∧ ... ∧ (xn ∧ yn) ∨ (¬xn ∧ yn)
```julia
n = 10
@satvariable(x[1:n], Bool)
@satvariable(y[1:n], Bool)
expr = (x .∧ y) .∨ (¬x .∧ y)
status = sat!(expr, solver=Z3())
println("x = $(value(x)), y = $(value(y))”)
```

### Investigating rounding of real numbers
This problem (from Microsoft's [Z3 tutorials](https://microsoft.github.io/z3guide/docs/theories/Arithmetic)) uses mixed integer and real variables to figure out whether there exists a constant `a` and two real numbers `xR` and `yR` such that `round(xR) +  round(yR)  > a` while `xR + yR < a`.
```julia
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

### Uninterpreted functions
An uninterpreted function is a function where the input-to-output mapping isn't known. The task of the SMT solver is to find this mapping such that some logical statements hole true. Let's find out if there exists a function `f(x)` such that `f(f(x)) == x`, `f(x) == y` and `x != y`.

```julia
@satvariable(x, Bool)
@satvariable(y, Bool)
@uninterpreted(f, Bool, Bool)

# Yices requires setting the logic manually. Here we set it to "QF_UFLIA" - "Quantifier free uninterpreted functions, linear integer arithmetic".
status = sat!(distinct(x,y), f(x) == y, f(f(x)) == x, solver=Yices(), logic="QF_UFLIA")
println("status = \$status")
```

The problem is `:SAT`, so there is such a function! Since the satisfying assignment for an uninterpreted function is itself a function, Satisfiability.jl sets the value of `f` to this function. Now calling `f(value)` returns the value of this satisfying assignment.

```julia
println(f(x.value))               # prints 0
println(f(x.value) == y.value)    # true
println(f(f(x.value)) == x.value) # true
```

### Proving a bitwise version of de Morgan's law.
In this example we want to show there is NO possible value of x and y such that de Morgan's bitwise law doesn't hold.
```julia
@satvariable(x, BitVector, 64)
@satvariable(y, BitVector, 64)

expr = not((~x & ~y) == ~(x | y))

status = sat!(expr, solver=Z3())
println(status) # if status is UNSAT we proved it.
```

## Development status
Release 0.1.1 is out! You can install it with the command `using Pkg; Pkg.add("Satisfiability")`. Please help make the Julia ecosystem better for everyone by opening a GitHub issue if you have feedback or find a bug.
