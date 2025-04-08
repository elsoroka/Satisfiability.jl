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

```jldoctest label3; output = false
using Satisfiability
@satvariable(nodes[1:4], Int)

# "There are 3 colors available"
limits = and.(nodes .>= 1, nodes .<= 3)

# "No adjacent nodes can share a color"
(a, b, c, d) = nodes
connections = and(a != b, a != c, b != c, c != d)

# "All 3 colors must be used"
# (If you leave this out you can find 24 colorings. But 12 of them will use only 2 colors.)
all3 = and(or(nodes .== i) for i=1:3)

# output

and_39aa6c16a6ff9055
 | or_9f04d9d45d8ef53c
 |  | eq_3ba7243db0822c90
 |  |  | nodes_3
 |  |  | const_2 = 2
 |  | eq_b73c73a1583deb0e
 |  |  | nodes_4
 |  |  | const_2 = 2
 |  | eq_e1f6b79aadf9ad44
 |  |  | nodes_1
 |  |  | const_2 = 2
 |  | eq_e874c19f88c4d856
 |  |  | nodes_2
 |  |  | const_2 = 2
 | or_a15b5775e03d4244
 |  | eq_4cc33d3bd343bd9d
 |  |  | nodes_4
 |  |  | const_3 = 3
 |  | eq_566bb555fc5ebd38
 |  |  | nodes_3
 |  |  | const_3 = 3
 |  | eq_76797323bb0791a8
 |  |  | nodes_1
 |  |  | const_3 = 3
 |  | eq_7c56cb6cd649a059
 |  |  | nodes_2
 |  |  | const_3 = 3
 | or_ad16424c3a0a7cb2
 |  | eq_3d803195e4b6c8b0
 |  |  | nodes_3
 |  |  | const_1 = 1
 |  | eq_439f0dac82766cac
 |  |  | nodes_2
 |  |  | const_1 = 1
 |  | eq_8e2938d86765bdbf
 |  |  | nodes_4
 |  |  | const_1 = 1
 |  | eq_b7ad036649f4b598
 |  |  | nodes_1
 |  |  | const_1 = 1
```

To find **all** the solutions, we have to exclude solutions as we find them. Suppose we find a satisfying assignment `[vars] = [values]`. Adding the negation `not(and(vars .== values))` to the list of assertions excludes that specific assignment from being found again. Remember: when excluding solutions, negate the whole expression. An easy mistake is `and(not(nodes .== value(nodes)))`, which excludes each node from taking on the particular value we just found (for example, saying "a cannot be 1", "b cannot be 2"...) instead of excluding the specific combination of all 4 values ("a cannot be 1 when b is 2,...").

```jldoctest label3; output = false
function findall()

    solutions = []
    open(Z3()) do interactive_solver # the do syntax closes the solver
        assert!(interactive_solver, limits, connections, all3)
        i = 1
        status, assignment = sat!(interactive_solver)
        while status == :SAT
            # Try to solve the problem
            push!(solutions, assignment)
            println("i = $i, status = $status, assignment = $assignment")
            assign!(nodes, assignment)
            
            # Use assert! to exclude the solution we just found.
            assert!(interactive_solver, not(and(nodes .== value(nodes))))
            status, assignment = sat!(interactive_solver)
            i += 1
        end
    end
    println("Found them all!")
end

findall()

# output

i = 1, status = SAT, assignment = Dict{Any, Any}("nodes_1" => 3, "nodes_2" => 2, "nodes_4" => 2, "nodes_3" => 1)
i = 2, status = SAT, assignment = Dict{Any, Any}("nodes_1" => 3, "nodes_2" => 2, "nodes_4" => 3, "nodes_3" => 1)
i = 3, status = SAT, assignment = Dict{Any, Any}("nodes_1" => 2, "nodes_2" => 3, "nodes_4" => 3, "nodes_3" => 1)
i = 4, status = SAT, assignment = Dict{Any, Any}("nodes_1" => 2, "nodes_2" => 3, "nodes_4" => 2, "nodes_3" => 1)
i = 5, status = SAT, assignment = Dict{Any, Any}("nodes_1" => 2, "nodes_2" => 1, "nodes_4" => 1, "nodes_3" => 3)
i = 6, status = SAT, assignment = Dict{Any, Any}("nodes_1" => 2, "nodes_2" => 1, "nodes_4" => 2, "nodes_3" => 3)
i = 7, status = SAT, assignment = Dict{Any, Any}("nodes_1" => 1, "nodes_2" => 3, "nodes_4" => 1, "nodes_3" => 2)
i = 8, status = SAT, assignment = Dict{Any, Any}("nodes_1" => 3, "nodes_2" => 1, "nodes_4" => 1, "nodes_3" => 2)
i = 9, status = SAT, assignment = Dict{Any, Any}("nodes_1" => 1, "nodes_2" => 2, "nodes_4" => 1, "nodes_3" => 3)
i = 10, status = SAT, assignment = Dict{Any, Any}("nodes_1" => 1, "nodes_2" => 2, "nodes_4" => 2, "nodes_3" => 3)
i = 11, status = SAT, assignment = Dict{Any, Any}("nodes_1" => 3, "nodes_2" => 1, "nodes_4" => 3, "nodes_3" => 2)
i = 12, status = SAT, assignment = Dict{Any, Any}("nodes_1" => 1, "nodes_2" => 3, "nodes_4" => 3, "nodes_3" => 2)
Found them all!
```