# Functions
```@contents
Pages = ["functions.md"]
Depth = 3
```

## Defining Boolean Variables
```@docs
Bool(name::String)
```

## Logical Operations
```@docs
¬(z::BoolExpr)
∧(z1::BoolExpr, z2::BoolExpr)
∨(z1::BoolExpr, z2::BoolExpr)
⟹(z1::BoolExpr, z2::BoolExpr)

all(zs)
any(zs)
```

## Generating the SMT representation of a problem
```@docs
declare(z::BoolExpr)
smt(zs::Array{T}) where T <: BoolExpr
save(prob::BoolExpr; filename="out")
```
## Solving a SAT problem

```@docs
sat!(prob::BoolExpr)
value(zs::Array{T}) where T <: AbstractExpr
```
