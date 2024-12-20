# Install Problem

This tutorial demonstrates how to solve the Install Problem, which involves determining
whether a set of software packages can be installed on a system given a set of dependencies
and conflicts. The install problem was introduced in the paper
[OPIUM: Optimal Package Install/Uninstall Manager](https://ieeexplore.ieee.org/document/4222580).

# Problem Description

A typical software distribution includes a collection of packages, each associated with
metadata describing its requirements. This metadata contains:

- **Dependencies**: Packages that must be installed for a given package to function.
- **Conflicts**: Packages that cannot coexist with the given package.

The goal is to determine whether a valid installation profile can be constructed that
satisfies all dependency and conflict constraints.

# Example Metadata

For example, consider a distribution with the following packages and rules:

- Package a depends on packages b, c, and z.
- Package b depends on package d.
- Package c depends on at least one of (d, e) and one of (f, g).
- Package d conflicts with package e.

# Constraints Representation

The above rules can be represented as logical constraints:

- ¬a∨b¬a∨b
- ¬a∨c¬a∨c
- ¬a∨z¬a∨z
- ¬b∨d¬b∨d
- ¬c∨(d∨e)¬c∨(d∨e)
- ¬c∨(f∨g)¬c∨(f∨g)
- ¬d∨¬e¬d∨¬e

These logical constraints form the basis for solving the problem using satisfiability (SAT) solvers.

# Dependency Graph and Conflicts

The metadata rules can also be visualized using a Dependency Graph and Conflict Relationships. To
represent both dependencies and conflicts in a single graph:

```
        (a)
       / | \
     (b) (c) (z)
       |    | \
      (d)  (d) (e)
       |     |   |
       |    (f) (g)
       |_________|
Conflicts:
(d) --- (e)
```
# Solving the Install Problem

Here’s the program that defines the metadata rules and solves the problem:

```jldoctest label3; output = false
using Satisfiability
@satvariable(a, Bool)
@satvariable(b, Bool)
@satvariable(c, Bool)
@satvariable(d, Bool)
@satvariable(e, Bool)
@satvariable(f, Bool)
@satvariable(g, Bool)
@satvariable(z, Bool)

function DependsOn(pack, deps)
    if typeof(deps) <: AbstractExpr
        return implies(pack, deps)
    else
        return and([implies(pack, dep) for dep in deps]...)
    end
end

function Conflict(packs...)
    return or([not(pack) for pack in packs]...)
end

function install_check(constraints...)
    open(Z3()) do solver
        # Assert constraints
        for constraint in constraints
            assert!(solver, constraint)
        end
        status, model = sat!(solver)
        println(status)
        for (key, value) in model
            println("$key => $value")
        end
   end
end


# Example 1: Section 2 of https://ieeexplore.ieee.org/document/4222580
install_check(
    DependsOn(a, [b, c, z]),
    DependsOn(b, [d]),
    DependsOn(c, [or(d, e), or(f, g)]),
    Conflict(d, e),
    a,
    z
)

# output

SAT
f => true
g => false
c => true
e => false
b => true
z => true
a => true
d => true
```
