# Pushing and popping assertions
In this problem we have some expressions we need to satisfy, and some that we would like to satisfy (but we can't satisfy them all).
We want to figure out which expressions we can satisfy using push() and pop() to assert and remove them as necessary.

```jldoctest label1; output = false
using Satisfiability
@satvariable(x, Bool)
@satvariable(y, Bool)
@satvariable(z, Bool)
necessary_exprs = or(and(not(x), y, z), and(not(y), x, z))

interactive_solver = open(Z3())

# We assert this at the first level, since we always have to have it.
assert!(interactive_solver, necessary_exprs)

# output


```

Here are some conflicting expressions. One of them is satisfiable when `necessary_exprs` is true; the others are not.
```jldoctest label1; output = false
conflicting_exprs = [
    not(z),
    and(not(x), not(y)),
    not(x),
    and(x,y),
]

# We'll use `push` and `pop` to add and remove them one at a time.

for e in conflicting_exprs
    # Push one assertion level on the stack
    push!(interactive_solver)

    # Now assert an expression that might make the problem unsatisfiable
    assert!(interactive_solver, e)
    status, assignment = sat!(interactive_solver)

    if status == :SAT
        println("We found it! Expr \n$e \nis satisfiable.")
        assign!(necessary_exprs, assignment)
        assign!(conflicting_exprs, assignment)
    else
        # Pop one level off the stack, removing the problematic assertion.
        pop!(interactive_solver)
    end
end

# output

We found it! Expr 
not_53b20e3050918288
 | x
 
is satisfiable.
```

### Another way to do this.
Let's reset the solver so we can try another way to do the same thing. This command clears all assertions, including the first one we made at level 1.
```jldoctest label1
reset_assertions!(interactive_solver)

# output


```

This time, we use `sat!(solver, exprs...)` which is equivalent to the SMT-LIB command `(check-sat-assuming exprs...)`. Thus the expression is not asserted but is assumed within the scope of the `sat!` call.
```jldoctest label1
assert!(interactive_solver, necessary_exprs)
# Here's an equivalent way to do this by passing exprs into sat!. This is equivalent to the SMT-LIB syntax "(check-sat-assuming (exprs...))", which does not (assert) the expressions but assumes they should be satisfied.
for e in conflicting_exprs
    status, assignment = sat!(interactive_solver, e)
    println("status = $status")
    if status == :SAT
        println("We found it! Expr \n$e \nis satisfiable.")
        assign!(necessary_exprs, assignment)
        assign!(conflicting_exprs, assignment)
    end
end

# We're done, so don't forget to clean up.
close(interactive_solver)

# output

status = ERROR
status = UNSAT
status = SAT
We found it! Expr 
not_53b20e3050918288 = true
 | x = false
 
is satisfiable.
status = UNSAT
```