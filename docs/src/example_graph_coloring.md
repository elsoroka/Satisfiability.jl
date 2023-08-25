# Graph coloring
A classic problem in graph theory is figuring out how to color nodes of a graph such that no two adjacent nodes have the same color.
This is useful for things like mapmaking (imagine if your map had two adjacent countries sharing a color!)
The [chromatic polynomial](https://en.wikipedia.org/wiki/Graph_coloring) counts the number of ways a graph can be colored using n colors. For example, this graph
```
 (a)
  | \
  | (c)--(d)
  | /
 (b)
```
can be colored using exactly 3 colors in 12 different ways. Let's use SMT to find all 12 ways to color this graph.

```julia
using Satisfiability
@satvariable(nodes[1:4], Int)

# "There are 3 colors available"
limits = and.(nodes .>= 1, nodes .<= 3)

# "No adjacent nodes can share a color"
(a, b, c, d) = nodes
connections = and(distinct(a, b), distinct(a, c), distinct(b, c), distinct(c, d))

# "All 3 colors must be used"
# (If you leave this out you can find 24 colorings. But 12 of them will use only 2 colors.)
all3 = and([or(nodes .== i) for i=1:3])
```

To find **all** the solutions, we have to exclude solutions as we find them. Suppose we find a satisfying assignment `[vars] = [values]`. Adding the negation `not(and(vars .== values))` to the list of assertions excludes that specific assignment from being found again. Remember: when excluding solutions, negate the whole expression. An easy mistake is `and(not(nodes .== value(nodes)))`, which excludes each node from taking on the particular value we just found (for example, saying "a cannot be 1", "b cannot be 2"...) instead of excluding the specific combination of all 4 values ("a cannot be 1 when b is 2,...").

```julia
function findall()

    solutions = []
    interactive_solver = open(Z3())
    assert!(interactive_solver, limits, connections, all3)
    i = 1
    while true
        # Try to solve the problem
        status, assignment = sat!(interactive_solver)

        if status == :SAT
            push!(solutions, assignment)
            println("i = $i, status = $status, assignment = $assignment")
            assign!(nodes, assignment)
            
            # Use assert! to exclude the solution we just found.
            assert!(interactive_solver, not(and(nodes .== value(nodes))))
        else
            close(interactive_solver)
            println("Found them all!")
            break
        end
        i += 1
    end
end

findall()
```