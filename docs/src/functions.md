# Functions
```@contents
Pages = ["functions.md"]
Depth = 3
```

## Defining variables
Use the `@satvariable` macro to define a variable.
```@docs
@satvariable
```
Satisfiability.jl currently supports propositional logic, integer and real-valued arithmetic, and bitvectors. Support for additional SMT-LIB theories is planned in future versions.
```@docs
BoolExpr(name::String)
IntExpr(name::String)
RealExpr(name::String)
BitVectorExpr(name::String, length::Int)
```

An **uninterpreted function** is a function where the mapping between input and output is not known. The task of the SMT solver is then to determine a mapping such that some SMT expression holds true.
```@docs
@uninterpreted
```


## Logical operations
These are operations in the theory of propositional logic. For a formal definition of this theory, see Figure 3.2 in [*The SMT-LIB Standard, Version 2.6*](https://smtlib.cs.uiowa.edu/standard.shtml) or the SMT-LIB [Core theory declaration](http://smtlib.cs.uiowa.edu/theories.shtml).
```@docs
not(z::BoolExpr)
and(z1::BoolExpr, z2::BoolExpr)
or(z1::BoolExpr, z2::BoolExpr)
xor(zs_mixed::Array{T}; broadcast_type=:Elementwise) where T

implies(z1::BoolExpr, z2::BoolExpr)
iff(z1::BoolExpr, z2::BoolExpr)
ite(x::BoolExpr, y::BoolExpr, z::BoolExpr)
distinct(z1::BoolExpr, z2::BoolExpr)
```

## Arithmetic operations
These are operations in the theory of integer and real-valued arithmetic.

Note that `+`, `-`, and `*` follow type promotion rules: if both `a` and `b` are `IntExpr`s, `a+b` will have type `IntExpr`. If either `a` or `b` is a `RealExpr`, the result will have type `RealExpr`. Integer division `div(a,b)` is defined only for `IntExpr`s. Real-valued division `a\b` is defined only in the theory of real-valued arithmetic.
For a formal definition of the theory of integer arithmetic, see Figure 3.3 in *The SMT-LIB Standard, Version 2.6*.

```@docs
Base.:-(a::IntExpr)
Base.abs(a::IntExpr)
Base.:+(a::IntExpr, b::IntExpr)
Base.:-(a::IntExpr, b::IntExpr)
Base.:*(a::RealExpr, b::RealExpr)
Base.div(a::IntExpr, b::IntExpr)
Base.mod(a::IntExpr, b::IntExpr)
Base.:/(a::RealExpr, b::RealExpr)
```

### Comparison operators
These operators are available for `IntExpr`, `RealExpr`, and `BitVector` SMT variables.
```@docs
Base.:(==)(a::IntExpr, b::IntExpr)
```
For BitVector variables, the comparison operators implement unsigned comparison as defined in the SMT-LIB standard [theory of BitVectors](http://smtlib.cs.uiowa.edu/theories.shtml).

```@docs
Base.:<(a::IntExpr, b::IntExpr)
Base.:<=(a::IntExpr, b::IntExpr)
Base.:>(a::IntExpr, b::IntExpr)
Base.:>=(a::IntExpr, b::IntExpr)
```

### Conversion operators
```@docs
to_int(a::RealExpr)
to_real(a::IntExpr)
```

## BitVector
```julia
    @satvariable(a, BitVector, 16)
    @satvariable(b, BitVector, 12)

    a + concat(bvconst(0x0, 4), b)
```
The SMT-LIB standard BitVector is often used to represent operations on fixed-size integers. Thus, BitVectorExprs can interoperate with Julia's native Integer, Unsigned and BigInt types.

### Bitwise operators
In addition to supporting the comparison operators above and arithmetic operators `+`, `-`, and `*`, the following BitVector-specific operators are available.
Note that unsigned integer division is available using `div`. Signed division is `sdiv`.
```@docs
div(a::AbstractBitVectorExpr, b::AbstractBitVectorExpr)
sdiv(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
```

The bitwise logical operator symbols `&`, `~` and `|` are provided for BitVector types instead of the Boolean logic symbols. This matches Julia's use of bitwise logical operators for Unsigned integer types.

```@docs
Base.:~(a::BitVectorExpr{UInt8})
Base.:|(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
Base.:&(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
nor(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
nand(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
xnor(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
Base.:<<(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
Base.:>>(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
Base.:>>>(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
urem(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
srem(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
smod(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
```
Signed comparisons.
```@docs
slt(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
sle(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
sgt(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
sge(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
```

The following word-level operations are also available in the SMT-LIB standard, either as core operations or defined in the [SMT-LIB BitVector logic](https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV).
```@docs
concat(a::Array{T}) where T
repeat(a::BitVectorExpr{UInt8}, n::Int64)
Base.getindex(a::BitVectorExpr{UInt8}, ind::UnitRange{Int64})
bv2int(a::BitVectorExpr{UInt8})
int2bv(a::IntExpr, s::Int)
bvcomp(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
zero_extend(a::BitVectorExpr{UInt8}, n::Int64)
sign_extend(a::BitVectorExpr{UInt8}, n::Int64)
rotate_left(a::BitVectorExpr{UInt8}, n::Int64)
rotate_right(a::BitVectorExpr{UInt8}, n::Int64)
```

### Utility functions for BitVectors
```@docs
bitcount(a::Integer)
nextsize(n::Integer)
bvconst(c::Integer, size::Int)
```

## Generating the SMT representation of a problem

```@docs
smt(zs::Array{T}) where T <: BoolExpr
save(prob::BoolExpr)
```
## Solving a SAT problem

```@docs
sat!(prob::Array{T}) where T <: BoolExpr
sat!(solver::InteractiveSolver)
value(zs::Array{T}) where T <: AbstractExpr
```

### Interacting with solvers
```@docs
open(solver::Solver)
close(solver::InteractiveSolver)
push!(solver::InteractiveSolver, n::Integer)
pop!(solver::InteractiveSolver, n::Integer)
assert!(solver::InteractiveSolver, exprs::BoolExpr)
sat!(solver::InteractiveSolver, exprs::BoolExpr)
send_command(solver::InteractiveSolver, cmd::String)
nested_parens_match(solver_output::String)
is_sat_or_unsat(solver_output::String)
parse_model(model::String)
assign!(e::AbstractExpr, d::Dict)
reset!(s::InteractiveSolver)
reset_assertions!(s::InteractiveSolver)
```

## Miscellaneous functions
```@docs
isequal(a::AbstractExpr, b::AbstractExpr)
```