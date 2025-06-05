# Solving SMT Problems in Julia
Satisfiability.jl is a package for representing [Boolean satisfiability (SAT)](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem) and selected other [satisfiability modulo theories (SMT)](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) problems in Julia. This package provides a simple front-end interface to common [SMT solvers](https://smt-lib.org/solvers.shtml), including full support for vector-valued and matrix-valued expressions.

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
* `or(z1, z2)` or `z1 ∨ z2`. The n-ary version, `or(z1,...,zn)`, is also available.
* `implies(z1, z2)` or `z1 ⟹ z2`.

These expressions can be nested to produce formulae of arbitrary complexity.

### SAT problems
Given a Boolean expression, the associated SAT problem can be posed as:

**"Is there a satisfying assignment of literals (1's and 0's) such that this formula is true?"**

* If this assignment exists, we say the formula is **satisfiable**. More than one satisfying assignment may exist for a given formula.

* If the assignment does not exist, we say the formula is **unsatisfiable**.

### SMT problems
Satisfiability modulo theories is a superset of Boolean satisfiability. SMT encompasses many other theories besides Boolean logic, several of which are supported here.

In the [theory of integers](https://smt-lib.org/theories-Ints.shtml), we can define integer-valued variables and operations such as `+`, `-`, `*` and the comparisons `<`, `<=`, `==`, `=>`, `>`. For example, we could determine whether there exists a satisfying assignment for integers `a` and `b` such that `a <= b, b <= 1 and a + b >= 2`. (There is - set `a = 1` and ` b = 1`.)

In the [theory of reals](https://smt-lib.org/theories-Reals.shtml), we can define real-valued variables and operations. Reals use the same operations as integers, plus division (`\`). However, algorithms to solve SMT problems over real variables are often slow and not guaranteed to find a solution. If you have a problem over only real-valued variables, you should use [JuMP](https://jump.dev/) and a solver like Gurobi instead.

In the [theory of fixed-length BitVectors](https://smt-lib.org/theories-FixedSizeBitVectors.shtml) one can prove properties over BitVectors, which are useful for representing fixed-size integer arithmetic. For example, you can use formal verification to prove correctness of your code - or discover bugs (some examples [here](https://sat-smt.codes code/SAT_SMT_by_example.pdf)), like [the sneaky Binary Search bug that went undetected for 20 years](https://thebittheories.com/the-curious-case-of-binary-search-the-famous-bug-that-remained-undetected-for-20-years-973e89fc212?gi=5adc69f5db4d).

SMT extends to other theories including [IEEE floating-point numbers](https://smt-lib.org/theories-FloatingPoint.shtml), [arrays](https://smt-lib.org/theories-ArraysEx.shtml) and [strings](https://smt-lib.org/theories-UnicodeStrings.shtml). While this package is still under development, we plan to implement support for the [SMT-LIB standard theories](http://smtlib.cs.uiowa.edu/theories.shtml) and operations.

## How does Satisfiability.jl work?
Satisfiability.jl provides an **interface** to SAT solvers that accept input in the [SMTLIB2](http://www.smtlib.org/) format. It works by generating the SMT representation of your problem, then invoking a solver to read said file.

Using this package, you should be able to interact with any solver that implements the [SMT-LIB standard](https://smt-lib.org/standard.shtml). We currently test with [Z3](https://microsoft.github.io/z3guide/) and [CVC5](https://cvc5.github.io/).
