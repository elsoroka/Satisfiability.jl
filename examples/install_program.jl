push!(LOAD_PATH, "../src")
using Satisfiability

# The Install Problem is a common scenario in software package management systems. The problem
# involves determining whether a set of software packages can be installed on a system, subject
# to two types of constraints:

# 1) Dependencies: Packages that must be installed alongside a given package.
# 2) Conflicts: Packages that cannot coexist on the system.

# This problem can be represented as a Boolean satisfiability (SAT) problem, which is ideal for
# efficient constraint-solving using SAT solver The install problem was introduced in the paper
# [OPIUM: Optimal Package Install/Uninstall Manager](https://ieeexplore.ieee.org/document/4222580).

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

# Example 2
install_check(DependsOn(a, [b, c, z]),
              DependsOn(b, d),
              DependsOn(c, [or(d, e), or(f, g)]),
              Conflict(d, e),
              Conflict(d, g),
              a,
              z)

# Example 3
install_check(
    DependsOn(a, [b, c, z]),
    DependsOn(b, d),
    DependsOn(c, [or(d, e), or(f, g)]),
    Conflict(d, e),
    Conflict(d, g),
    a,
    z,
    g  # Adding a condition to install g
)
