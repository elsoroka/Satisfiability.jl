# Functions
```@contents
Pages = ["functions.md"]
Depth = 3
```
Test link [link](#Logical-Operations)

## Defining variables
The preferred way to define a variable is
```@docs
@satvariable
```

This alternate syntax is also available.
```@docs
Bool(name::String)
Int(name::String)
Real(name::String)
```

## Logical operations
These are operations in the theory of propositional logic. For a formal definition of this theory, see Figure 3.2 in *The SMT-LIB Standard, Version 2.6*.
```@docs
not(z::BoolExpr)
and(z1::BoolExpr, z2::BoolExpr)
or(z1::BoolExpr, z2::BoolExpr)
xor(zs_mixed::Array{T}; broadcast_type=:Elementwise) where T

implies(z1::BoolExpr, z2::BoolExpr)
iff(z1::BoolExpr, z2::BoolExpr)
ite(x::Union{BoolExpr, Bool}, y::Union{BoolExpr, Bool}, z::Union{BoolExpr, Bool})

all(zs::Array{T}) where T <: BoolExpr
any(zs::Array{T}) where T <: BoolExpr
```

## Arithmetic operations
These are operations in the theory of integer and real-valued arithmetic.

Note that `+`, `-`, and `*` follow type promotion rules: if both `a` and `b` are `IntExpr`s, `a+b` will have type `IntExpr`. If either `a` or `b` is a `RealExpr`, the result will have type `RealExpr`. Division `\` is defined only in the theory of real-valued arithmetic, thus it always has return type `RealExpr`.
For a formal definition of the theory of integer arithmetic, see Figure 3.3 in *The SMT-LIB Standard, Version 2.6*.

```@docs
Base.:-(a::IntExpr)
Base.:+(a::IntExpr, b::IntExpr)
Base.:-(a::IntExpr, b::IntExpr)
Base.:*(a::RealExpr, b::RealExpr)
Base.:/(a::RealExpr, b::RealExpr)
```

### Comparison operators
`Base.==` - Method
```julia
    a  == b
    a == 1.0
```
Returns the Boolean expression a == b (arithmetic equivalence). Use dot broadcasting for vector-valued and matrix-valued expressions.

```julia
@satvariable(a[1:n], :Int)
@satvariable(b[1:n, 1:m], :Int)
a .== b
```

**Note:** To test whether two `AbstractExpr`s are eqivalent (in the sense that all properties are equal, not in the shared-memory-location sense of `===`), use `isequal`.

```@docs
Base.:<(a::AbstractExpr, b::AbstractExpr)
Base.:<=(a::AbstractExpr, b::AbstractExpr)
Base.:>(a::AbstractExpr, b::AbstractExpr)
Base.:>=(a::AbstractExpr, b::AbstractExpr)
```

## Generating the SMT representation of a problem

```@docs
smt(zs::Array{T}) where T <: BoolExpr
save(prob::BoolExpr; filename="out")
```
## Solving a SAT problem

```@docs
sat!(prob::BoolExpr, solver::Solver)
value(zs::Array{T}) where T <: AbstractExpr
```

### Custom interactions with solvers:
```@docs
open_solver(solver::Solver)
send_command(pstdin::Pipe, pstdout::Pipe, cmd::String)
nested_parens_match(solver_output::String)
```

## Miscellaneous functions
```@docs
Base.isequal(a::AbstractExpr, b::AbstractExpr)
```