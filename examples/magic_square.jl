push!(LOAD_PATH, "../src")
using Satisfiability

function magic_square(n)
    # The magic constant for the square
    magic = n * (n^2 + 1) ÷ 2

    open(Z3()) do solver
        # The magic square as a grid of integer variables
        @satvariable(matrix[1:n, 1:n], Int)

        # Each cell must be in the range 1 to n²
        for r in 1:n, c in 1:n
            assert!(solver, and(1 ≤ matrix[r, c], matrix[r, c] ≤ n^2))
        end

        # All values in the matrix must be distinct
        mat = [matrix[r, c] for r in 1:n, c in 1:n]
        assert!(solver, distinct(mat))

        # Sum of rows and columns must equal the magic constant
        for i in 1:n
            assert!(solver, sum(matrix[i, :]) == magic) # Row sums
            assert!(solver, sum(matrix[:, i]) == magic) # Column sums
        end

        # Diagonal sums must equal the magic constant
        diag1 = [matrix[i, i] for i in 1:n]
        diag2 = [matrix[i, n - i + 1] for i in 1:n]
        assert!(solver, sum(diag1) == magic)
        assert!(solver, sum(diag2) == magic)

        status, solution = sat!(solver)
        println(status)
        matrix = zeros(Int, n, n)
        for (key, value) in solution
            parts = split(key, "_")
            row, col = parse(Int, parts[2]), parse(Int, parts[3])
            matrix[row, col] = value
        end
        for row in 1:n
            println(join(matrix[row, :], " | "))
        end
    end
end


magic_square(3)
magic_square(4)
