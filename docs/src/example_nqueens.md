# N-Queens

The [N-Queens puzzle](https://en.wikipedia.org/wiki/Eight_queens_puzzle)
asks you to place `N` queens on an `N×N` chessboard such that no two queens
threaten each other. This means:

- No two queens can be in the same row.
- No two queens can be in the same column.
- No two queens can share the same diagonal.

This is a classical Satisfiability Problem (SAT), where the goal is to find a truth
assignment for Boolean variables that satisfies a set of logical constraints. In SAT,
each variable can be either true or false, and constraints are logical expressions
that must evaluate to true for the problem to be solved.

# Solution

To solve the `N`-Queens problem using SAT, we must express the problem's constraints as
logical formulas and then use a SAT solver to find an assignment of Boolean variables
that satisfies all the constraints.

- **Variables**:
  - Each queen is assigned a position on the board, represented by Boolean variables. For a
board with `N` rows and `N` columns, we use a 2D array of size `N × N`, where `Q[i, j]` is
true if there's a queen at position `(i, j)`.
- **Constraints**:
  - Each row must contain exactly one queen.
  - Each column must contain exactly one queen.
  - No two queens can share the same diagonal

```jldoctest label3; output = false
using Satisfiability
function queens(n::Int)
    open(Z3()) do solver
        # Define SAT variables for the column positions of each queen
        @satvariable(Q[1:n], Int)

        # Each queen must be in a column within {1, ..., n}
        val_c = [(1 ≤ Q[i]) ∧ (Q[i] ≤ n) for i in 1:n]

        # All queens must be in distinct columns
        col_c = [distinct(Q)]

        # No two queens can attack each other diagonally
        diag_c = []
        for i in 1:n
            for j in 1:i-1
                push!(diag_c, ite(i == j, true, (Q[i] - Q[j] ≠ i - j) ∧ (Q[i] - Q[j] ≠ j - i)))
            end
        end

        # Add all constraints to the solver
        for constraint in vcat(val_c, col_c, diag_c)
            assert!(solver,constraint)
        end

        # Solve and print all solutions
        num_solutions = 0
        while true
            status, assignment = sat!(solver)
            if status != :SAT
                break
            end

            # Assign values to the variables and print the solution
            assign!(Q, assignment)
            solution = [value(Q[i]) for i in 1:n]
            println(solution)
            num_solutions += 1

            # Add a constraint to exclude the current solution
            exclusion = or([Q[i] ≠ solution[i] for i in 1:n]...)
            assert!(solver, exclusion)
        end

        println("Total solutions: $num_solutions")
    end
end

queens(4)

# output

[2, 4, 1, 3]
[3, 1, 4, 2]
Total solutions: 2
```
