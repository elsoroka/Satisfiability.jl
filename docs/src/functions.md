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
An **uninterpreted function** is a function where the mapping between input and output is not known. The task of the SMT solver is then to determine a mapping such that some SMT expression holds true.
```@docs
@uninterpreted
```


## Logical operations
These are operations in the theory of propositional logic. For a formal definition of this theory, see Figure 3.2 in *The SMT-LIB Standard, Version 2.6* or the SMT-LIB [Core theory declaration](http://smtlib.cs.uiowa.edu/theories.shtml).
```@docs
not(z::BoolExpr)
and(z1::BoolExpr, z2::BoolExpr)
or(z1::BoolExpr, z2::BoolExpr)
xor(zs_mixed::Array{T}; broadcast_type=:Elementwise) where T

implies(z1::BoolExpr, z2::BoolExpr)
iff(z1::BoolExpr, z2::BoolExpr)
ite(x::Union{BoolExpr, Bool}, y::Union{BoolExpr, Bool}, z::Union{BoolExpr, Bool})

distinct(z1::BoolExpr, z2::BoolExpr)

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

## BitVector
```julia
    @satvariable(a, BitVector, 16)
    @satvariable(b, BitVector, 12)

    a + concat(bvconst(0x0, 4), b)
```
The SMT-LIB standard BitVector is often used to represent operations on fixed-size integers. Thus, BitVectorExprs can interoperate with Julia's native Integer, Unsigned and BigInt types.

### Bitwise operators
In addition to supporting the comparison operators above and arithmetic operators `+`, `-`, and `*`, the following BitVector-specific operators are available.
Note that unsigned integer division is available using `div`.
```@docs
Base.div(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
```

The bitwise logical operator symbols `&`, `~` and `|` are provided for BitVector types instead of the Boolean logic symbols. This matches Julia's use of bitwise logical operators for Unsigned integer types.

```@docs
Base.:~(a::BitVectorExpr{UInt8})
Base.:|(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
Base.:&(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
Base.:<<(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
Base.:>>>(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
urem(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
```

The following word-level operations are also available in the SMT-LIB standard.
```@docs
concat(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
Base.getindex(a::BitVectorExpr{UInt8}, ind::UnitRange{Int64})
bv2int(a::BitVectorExpr{UInt8})
int2bv(a::IntExpr, s::Int)
```

### Utility functions for BitVectors
```@docs
bitcount(a::Integer)
nextsize(n::Integer)
bvconst(c::Integer, size::Int)
```

### Additional Z3 BitVector operators.
Z3 implements the following signed comparisons for BitVectors. Note that these are not part of the SMT-LIB standard and other solvers may not support them.
```@docs
Base.:>>(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
srem(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
smod(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
nor(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
nand(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
xnor(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
```

Signed comparisons are also Z3-specific.
```@docs
slt(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
sle(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
sgt(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
sge(a::BitVectorExpr{UInt8}, b::BitVectorExpr{UInt8})
```

## Generating the SMT representation of a problem

```@docs
smt(zs::Array{T}) where T <: BoolExpr
save(prob::BoolExpr, io::IO)
```
## Solving a SAT problem

```@docs
sat!(prob::BoolExpr, solver::Solver)
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