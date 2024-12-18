push!(LOAD_PATH, "../src")

using Satisfiability

# [Sudoku](https://en.wikipedia.org/wiki/Sudoku) is a classic puzzle that challenges players
# to fill a 9x9 grid with digits from 1 to 9. The objective is simple but challenging: each row,
# each column, and each 3x3 subgrid (also known as a "box") must contain the digits 1 through 9
# exactly once.

# Create a 9x9 matrix of integer variables (for the Sudoku grid)
@satvariable(X[1:9, 1:9], Int);

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

# Define the Sudoku puzzle instance using 0 for empty cells
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
]

# Constraints to set the values of the cells based on the puzzle instance
instance_c = [
    ite(instance[i][j] == 0, X[i, j] == X[i, j], X[i, j] == instance[i][j]) for i in 1:9, j in 1:9
];

# Combine the sudoku constraints and the puzzle instance constraints
constraints = vcat(sudoku_c..., instance_c...);

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
