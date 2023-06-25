# Functions
```@contents
Pages = ["functions.md"]
Depth = 3
```
Test link [link](#Logical-Operations)

## Defining Boolean Variables
```@docs
Bool(name::String)
```

## Logical Operations
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

## Generating the SMT representation of a problem
{#smt-representation}
```@docs
smt(zs::Array{T}) where T <: BoolExpr
save(prob::BoolExpr; filename="out")
```
## Solving a SAT problem

```@docs
sat!(prob::BoolExpr)
value(zs::Array{T}) where T <: AbstractExpr
```
