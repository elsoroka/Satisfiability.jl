# Interactive solving
```@contents
Pages = ["interactive.md"]
Depth = 3
```

The simplest way to solve an SMT problem is to call `sat!`. Under the hood, `sat!` translates your problem to the SMT-LIB format, spawns a solver in a new process, feeds in your problem and, if it's satisfiable, requests the satisfying assignment.

However, many use cases require ongoing interaction with the SMT solver. `Satisfiability.jl` provides this functionality using the `InteractiveSolver` struct, allowing users to interface with a running solver process. A typical interactive workflow looks like this.

**Construct some expressions**
```jldoctest label10; output = false
using Satisfiability
@satvariable(x, Bool)
@satvariable(y, Bool)
@satvariable(z, Bool)
expr1 = or(and(not(x), y), and(not(y), x))
expr2 = not(z)

# output

not_25ec308d1df79cdc
 | z
```

**Spawn a solver process and make some assertions.**
```jldoctest label10; output = false
interactive_solver = open(Z3())
assert!(interactive_solver, expr1, expr2)

# output


```
**Check satisfiability.**
In interactive solver mode, you can provide more expressions to `sat!`; this would look like `sat!(interactive_solver, expr3, expr4...)`.
Since `sat!` only receives the solver object, it's not able to set the values of `expr1` and `expr2`. Instead, it will return a dictionary containing the satisfying assignment. You can then set your expressions' values using `assign!`.
```jldoctest label10; output = false
status, assignment = sat!(interactive_solver)
if status == :SAT
    assign!(expr1, assignment)
    assign!(expr2, assignment)
    println("Values of x, y, z: x=$(value(x)), y=$(value(y)), z=$(value(z)))")
end

# output

Values of x, y, z: x=true, y=false, z=false)
```
**Do other stuff, then close your process.**
```jldoctest label10; output = false
close(interactive_solver)

# output


```

The [Graph Coloring](example_graph_coloring.md) example uses interactivity to find **every** solution to a problem.

## Managing the assertion stack
SMT-LIB implements the concept of an assertion stack. Pushing a level onto the stack allows you to assert statements, then pop that level off, erasing the assertions and declarations you made.
This is useful when incrementally adding constraints to a problem. [Finding Bad Assertions](example_bad_assertions.md) provides an example of using `push` and `pop` or `sat!(solver, exprs...)` to manage assertions.

### How can I get more control over the solver?
If you need more granular control over solver commands and responses, check our guide on [advanced usage](advanced.md). For suggestions, feel free to open a GitHub issue! This is a new package and we'd like to hear user feedback. 

!!! warning 
    Don't set print-success

If you set the SMT-LIB option `(set-option :print-success true)` it will confuse the output parser. Future versions of `Satisfiability.jl` will address this issue.
