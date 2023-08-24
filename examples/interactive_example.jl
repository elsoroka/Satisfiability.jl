push!(LOAD_PATH, "../src")
using Satisfiability

@satvariable(x, Bool)
@satvariable(y, Bool)
@satvariable(z, Bool)
expr1 = or(and(not(x), y), and(not(y), x))
expr2 = not(z)

# Spawn a solver process
interactive_solver = open(Z3())

# Make some assertions.
assert!(interactive_solver, expr1, expr2)

# Check satisfiability
status, assignment = sat!(interactive_solver)
if status == :SAT
    assign!(expr1, assignment)
    assign!(expr2, assignment)
    println("Values of x, y, z: x=$(value(x)), y=$(value(y)), z=$(value(z)))")
end

# Close your process
close(interactive_solver)