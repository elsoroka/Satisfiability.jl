push!(LOAD_PATH, "../src")
using Satisfiability

# A classic problem in graph theory is figuring out how to color nodes of a graph such that no two adjacent nodes have the same color.
# This is useful for things like mapmaking (imagine if your map had two adjacent countries sharing a color!)
# The chromatic polynomial (https://en.wikipedia.org/wiki/Graph_coloring) counts the number of ways a graph can be colored using n colors.
# For example, this graph
#=
 (a)
  | \
  | (c)--(d)
  | /
 (b)
=#
# can be colored using exactly 3 colors in 12 different ways.
# Let's use SMT to find all 12 ways to color this graph.

@satvariable(nodes[1:4], Int)

# "There are 3 colors available"
limits = and.(nodes .>= 1, nodes .<= 3)

# "No adjacent nodes can share a color"
(a, b, c, d) = nodes
connections = and(distinct(a, b), distinct(a, c), distinct(b, c), distinct(c, d))

# "All 3 colors must be used"
# (If you leave this out you can find 24 colorings. But 12 of them will use only 2 colors.)
all3 = and(or(nodes .== i) for i=1:3)

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
