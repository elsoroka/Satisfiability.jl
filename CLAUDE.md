# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this project is

Satisfiability.jl is a Julia package for representing and solving SAT/SMT problems. It provides a high-level DSL that compiles to SMT-LIB and calls external solvers (Z3, CVC5, Yices).

## Commands

**Run all tests:**
```bash
julia --project=. -e 'using Pkg; Pkg.test()'
```

**Run a single test file (from project root):**
```bash
julia --project=. test/boolean_operation_tests.jl
```

**Run tests with JET static analysis:**
```bash
JET_TEST=true julia --project=. -e 'using Pkg; Pkg.test()'
```

**Build docs locally:**
```bash
julia --project=docs docs/make.jl
```

**CI requires Z3 and Yices installed:**
```bash
sudo apt install z3 yices
```

## Architecture

### Expression tree

All SAT/SMT expressions are trees of `AbstractExpr`. The type hierarchy:
- `BoolExpr` — Boolean variables and operations (`:identity`, `:and`, `:or`, `:not`, `:xor`, `:iff`, `:implies`, `:ite`)
- `IntExpr`, `RealExpr` — numeric expressions (subtype `NumericExpr`)
- `BitVectorExpr{T}`, `SlicedBitVectorExpr{T}` — fixed-width bitvectors
- `UninterpretedFunc` — uninterpreted function applications

Each node stores: `op::Symbol`, `children::Array{AbstractExpr}`, `value` (nothing until solved), `name::String`.

### Key source files

| File | Role |
|------|------|
| `src/BoolExpr.jl` | `AbstractExpr` base, `BoolExpr` type, printing, hashing |
| `src/BooleanOperations.jl` | `and`, `or`, `not`, `xor`, `iff`, `implies`, `ite` |
| `src/IntExpr.jl` | `IntExpr`, `RealExpr` types and arithmetic/comparison ops |
| `src/BitVectorExpr.jl` | `BitVectorExpr{T}`, all bitvector-specific operations |
| `src/uninterpreted_func.jl` | `@uninterpreted` macro and function application |
| `src/smt_macros.jl` | `@satvariable` macro for variable declaration |
| `src/smt_representation.jl` | `declare()` and `smt()` — compile expression trees to SMT-LIB strings |
| `src/call_solver.jl` | `Solver`/`InteractiveSolver` types, stdin/stdout solver I/O |
| `src/sat.jl` | `sat!()` — top-level solve entry point, calls `talk_to_solver` |
| `src/utilities.jl` | Internal: name hashing, deduplication, `__get_hash_name` |
| `src/multiple_dispatch_ops.jl` | Broadcast and array overloads for all expression types |

### Data flow

1. User declares variables with `@satvariable x Bool` or `BoolExpr("x")`
2. Operators build expression trees (no SMT generated yet)
3. `sat!(expr)` → `smt(expr)` generates SMT-LIB string → passed to solver via stdin
4. Solver output parsed → `assign!(expr, values)` walks the tree to set `.value` fields

### Global state

`GLOBAL_VARNAMES` (in `Satisfiability.jl`) tracks declared variable names to warn on duplicates. Call `CLEAR_VARNAMES!()` between solves in loops. `SET_DUPLICATE_NAME_WARNING!(false)` suppresses warnings (used in tests).

### Solver interface

`Solver` is a simple struct with a name and command. `InteractiveSolver` wraps a persistent process for incremental solving via `push!`/`pop!`/`assert!`/`send_command`. Default solver is `Z3()` which uses `z3_jll`.

### Naming convention for compound expressions

`utilities.jl:__get_hash_name` generates deterministic names for intermediate expressions (e.g., `and(x,y)` → `AND_<hash>`). Commutative ops sort children before hashing so `and(x,y)` and `and(y,x)` get the same name.
