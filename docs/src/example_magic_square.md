# Magic Square

A **[Magic Square](https://en.wikipedia.org/wiki/Magic_square)** is a grid of distinct numbers
arranged such that the sums of the numbers in each row, each column, and the two diagonals are
equal. The sum is referred to as the **magic constant**.

### Setup

Given an integer `n`, the task is to fill an `n x n` grid with integers from `1` to `n²` such that:
- The sum of each row, column, and both diagonals equals the magic constant.
- All numbers are distinct.

The **magic constant** for an `n x n` magic square is calculated as: ``M = \frac{n \times (n^2 + 1)}``.
This problem can be formulated as a **satisfiability problem**  where we need to find the values of
the grid cells that satisfy certain constraints.

### Steps

1. **Variables**: We define variables for each cell in the `n x n` grid. These are integer variables
representing the values that will be filled in each cell.
2. **Constraints**:
   - Each cell must contain an integer between `1` and `n²`.
   - All numbers in the grid must be distinct.
   - The sum of each row, column, and the two diagonals must equal the magic constant.

3. **Solver**: We use a SAT solver to find an assignment of values to the grid that satisfies all
the constraints.

### Solution

```jldoctest label3; output = false
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

# output

SAT
8 | 1 | 6
3 | 5 | 7
4 | 9 | 2
```
