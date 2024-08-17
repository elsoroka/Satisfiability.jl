# Release Notes
```@contents
Pages = ["release_notes.md"]
Depth = 3
```
# Version 0.1.3 (Aug 16, 2024)
* Support Unicode variable names.
* Add experimental support for 3D tensor variables.

# Version 0.1.2 (May 23, 2024)
* Automatically download Z3 using `z3_jll` when Satisfiability.jl is installed.

# Version 0.1.1 (December 15, 2023)
* Fixed bugs in issues #21 and #26.
* Added remaining operators defined in SMT-LIB QF_BV (bitvector) specification (issue #22)
* Add `^` for square
* Correctly promote expressions containing mixed `BoolExpr`, `IntExpr` and `RealExpr` types. When a Boolean variable `z` is used in an arithmetic expression, it is rewritten to `ite(z 1 0)` (int) or `ite(z 1.0 0.0)` (real), which matches Z3's behavior. The SMT-LIB functions `to_real` and `to_int` are used to convert mixed `IntExpr`s and `RealExpr`s.

# Version 0.1.0 (August 27, 2023)
Initial release.
