push!(LOAD_PATH, "../src")
using Satisfiability

# The N-Queens puzzle is a classic combinatorial problem that requires placing N chess
# queens on an N×N chessboard such that no two queens threaten each other. The goal is
# to find all possible arrangements of the queens. This is a classical Satisfiability
# Problem (SAT), where the goal is to find a truth assignment for Boolean variables that
# satisfies a set of logical constraints.
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
queens(8)

