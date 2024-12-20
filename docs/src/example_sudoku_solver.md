# Sudoku

[Sudoku](https://en.wikipedia.org/wiki/Sudoku) is a classic puzzle that challenges players
to fill a 9x9 grid with digits from 1 to 9. The objective is simple but challenging: each row,
each column, and each 3x3 subgrid (also known as a "box") must contain the digits 1 through 9
exactly once.

In this tutorial, we will guide you through how to solve a Sudoku puzzle using Z3, a powerful SMT
(Satisfiability Modulo Theories) solver. Z3 is a tool for checking the satisfiability of logical
formulas, and it can be used to encode and solve problems like Sudoku efficiently.

We start by defining variables for each cell in the 9x9 Sudoku grid. These variables will
represent the digits in the grid.

```jldoctest label4; output = false
using Satisfiability
# Create a 9x9 matrix of integer variables (for the Sudoku grid)
@satvariable(X[1:9, 1:9], Int);
```

The main constraints for Sudoku are:

- *Cell*: Each cell must contain a value between 1 and 9.
- *Row*: Each row must contain distinct values (no repetitions).
- *Column*: Each column must contain distinct values.
- *Subgrid*: Each 3x3 subgrid must contain distinct values.

```jldoctest label4; output = false
# Each cell contains a value between 1 and 9
cells_c = [and(1 <= X[i, j], X[i, j] <= 9) for i in 1:9, j in 1:9];

# Each row contains distinct values
rows_c = [distinct(X[i, :]) for i in 1:9];

# Each column contains distinct values
cols_c = [distinct(X[:, j]) for j in 1:9];

# Each 3x3 square contains distinct values
sq_c = [distinct([X[3*i0 + i, 3*j0 + j] for i in 1:3, j in 1:3]) for i0 in 0:2, j0 in 0:2];

# Combine all constraints into one list
sudoku_c = vcat(cells_c..., rows_c..., cols_c..., sq_c...);
```

For a given Sudoku puzzle, some cells are pre-filled with known values, and others are
empty (usually represented by 0). We need to define constraints for these fixed cells to
ensure they hold their values. Let’s assume that the puzzle is provided as a 9x9 matrix
where 0 represents an empty cell:

```jldoctest label4; output = false
instance = [
    (5, 3, 0, 0, 7, 0, 0, 0, 0),
    (6, 0, 0, 1, 9, 5, 0, 0, 0),
    (0, 9, 8, 0, 0, 0, 0, 6, 0),
    (8, 0, 0, 0, 6, 0, 0, 0, 3),
    (4, 0, 0, 8, 0, 3, 0, 0, 1),
    (7, 0, 0, 0, 2, 0, 0, 0, 6),
    (0, 6, 0, 0, 0, 0, 2, 8, 0),
    (0, 0, 0, 4, 1, 9, 0, 0, 5),
    (0, 0, 0, 0, 8, 0, 0, 7, 9)
];
```

!!! note We have chosen the identical pre-filled values as presented in the
[JuMP.jl's tutorial] (https://jump.dev/JuMP.jl/stable/tutorials/linear/sudoku/),
where they apply a Mixed-integer linear programming approach to solve the Sudoku puzzle.

Define constraints for the given values (cells with non-zero values) as follows:
```jldoctest label4; output = false
# Constraints to set the values of the cells based on the puzzle instance
instance_c = [
    ite(instance[i][j] == 0, X[i, j] == X[i, j], X[i, j] == instance[i][j]) for i in 1:9, j in 1:9
];
```

Now, we combine all the constraints (cell, row, column, subgrid, and given values):

```jldoctest label4; output = false
# Combine the sudoku constraints and the puzzle instance constraints
constraints = vcat(sudoku_c..., instance_c...);
```

Now that we have set up all the constraints, we can use Z3 to solve the puzzle. The solver
will check if the constraints are satisfiable and, if so, provide the solution.

```jldoctest label4; output = false
function print_sudoku_solution(sudoku_dict)
    grid = zeros(Int, 9, 9)
    for (key, value) in sudoku_dict
        row, col = parse(Int, split(key, "_")[2]), parse(Int, split(key, "_")[3])
        grid[row, col] = value
    end
    for i in 1:9
        row_str = ""
        for j in 1:9
            row_str *= string(grid[i, j]) * " "
            if j % 3 == 0 && j != 9
                row_str *= "| "
            end
        end
        println(row_str)
        if i % 3 == 0 && i != 9
            println("-"^21)
        end
    end
end

# Now, we need to open the solver and pass the constraints properly
open(Z3()) do solver
    # Assert each constraint individually
    for constraint in constraints
        assert!(solver, constraint)
    end
    status, solution = sat!(solver)
    println("Status: ", status)
    print_sudoku_solution(solution)
end

# output
Status: SAT
5 3 4 | 6 7 8 | 9 1 2
6 7 2 | 1 9 5 | 3 4 8
1 9 8 | 3 4 2 | 5 6 7
---------------------
8 5 9 | 7 6 1 | 4 2 3
4 2 6 | 8 5 3 | 7 9 1
7 1 3 | 9 2 4 | 8 5 6
---------------------
9 6 1 | 5 3 7 | 2 8 4
2 8 7 | 4 1 9 | 6 3 5
3 4 5 | 2 8 6 | 1 7 9
```
