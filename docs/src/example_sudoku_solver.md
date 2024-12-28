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
println(size(X))

# output

(9, 9)
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
size(sudoku_c)

# output

(108,)
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
size(instance)

# output

(9,)
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

# output

9×9 Matrix{BoolExpr}:
 eq_dcf604d979b7fa47
 | X_1_1
 | const_5 = 5
  eq_308eaa2cff143be9
 | X_1_2
 | const_3 = 3
  …  eq_2d017e8e50553990
 | X_1_9
 | X_1_9

 eq_bbe7cfe32f2c86ce
 | X_2_1
 | const_6 = 6
  eq_9ce5ecacfb3d4995
 | X_2_2
 | X_2_2
           eq_ebc64589fcc890cc
 | X_2_9
 | X_2_9

 eq_db84c42bcfacc50e
 | X_3_1
 | X_3_1
        eq_58318b31d4f50cfb
 | X_3_2
 | const_9 = 9
     eq_95f73805835f69cb
 | X_3_9
 | X_3_9

 eq_d941bd305d656f1f
 | X_4_1
 | const_8 = 8
  eq_9b6cfb74f3852d3e
 | X_4_2
 | X_4_2
           eq_290cc45b1804d9df
 | X_4_9
 | const_3 = 3

 eq_a9de797a69e79898
 | X_5_1
 | const_4 = 4
  eq_39cc02fe88292601
 | X_5_2
 | X_5_2
           eq_8ae5b89d9de60fb9
 | X_5_9
 | const_1 = 1

 eq_36cfe09d42965739
 | X_6_1
 | const_7 = 7
  eq_e4cfdba84463e114
 | X_6_2
 | X_6_2
        …  eq_1187474addf2ab2e
 | X_6_9
 | const_6 = 6

 eq_4fbdfd428c370ae
 | X_7_1
 | X_7_1
         eq_b8bf46366043ab6d
 | X_7_2
 | const_6 = 6
     eq_147e360d5715143b
 | X_7_9
 | X_7_9

 eq_7e608dc16ec3aa85
 | X_8_1
 | X_8_1
        eq_c37b9f4b2b896e52
 | X_8_2
 | X_8_2
           eq_40e977cc36265ac6
 | X_8_9
 | const_5 = 5

 eq_350c35e834afcd83
 | X_9_1
 | X_9_1
        eq_39f8fa1801dc42df
 | X_9_2
 | X_9_2
           eq_29b7b29789ac23ed
 | X_9_9
 | const_9 = 9
```

Now, we combine all the constraints (cell, row, column, subgrid, and given values):

```jldoctest label4; output = false
# Combine the sudoku constraints and the puzzle instance constraints
constraints = vcat(sudoku_c..., instance_c...);

# output

189-element Vector{BoolExpr}:
 and_c744d09714c6b14d
 | leq_645af7f208a4da3c
 |  | X_1_1
 |  | const_9 = 9
 | leq_b9cca733c2dec3a6
 |  | const_1 = 1
 |  | X_1_1

 and_39b2ec5c0a615082
 | leq_77064d0c37cef03b
 |  | X_2_1
 |  | const_9 = 9
 | leq_7c949875888eaac
 |  | const_1 = 1
 |  | X_2_1

 and_9057b9b839281483
 | leq_643a45c9c4210ebd
 |  | const_1 = 1
 |  | X_3_1
 | leq_911d7fb062ce69ab
 |  | X_3_1
 |  | const_9 = 9

 and_6526834eb65fd333
 | leq_3d535577b3d0b8c8
 |  | X_4_1
 |  | const_9 = 9
 | leq_eeaf732a5182e069
 |  | const_1 = 1
 |  | X_4_1

 and_d9478c60aa64e7ef
 | leq_9b2ca968bc0ed01
 |  | const_1 = 1
 |  | X_5_1
 | leq_d559424db9872568
 |  | X_5_1
 |  | const_9 = 9

 and_cbf22e358992c26c
 | leq_a0655f0f4aa23067
 |  | X_6_1
 |  | const_9 = 9
 | leq_f4b1ab179c46d645
 |  | const_1 = 1
 |  | X_6_1

 and_c8a8bbef41ca3f99
 | leq_adf3e69c17355765
 |  | const_1 = 1
 |  | X_7_1
 | leq_beb8f736c1044207
 |  | X_7_1
 |  | const_9 = 9

 and_4fbec5152e86692f
 | leq_171cceb01a439470
 |  | const_1 = 1
 |  | X_8_1
 | leq_a7070fac90ae789a
 |  | X_8_1
 |  | const_9 = 9

 and_7dc45ca7c107f13d
 | leq_a4c536ae7698603f
 |  | const_1 = 1
 |  | X_9_1
 | leq_d5c1534f0ecfa75f
 |  | X_9_1
 |  | const_9 = 9

 and_ba21f78747952015
 | leq_5b23829fba9c70fd
 |  | const_1 = 1
 |  | X_1_2
 | leq_646aa29126778889
 |  | X_1_2
 |  | const_9 = 9

 and_5b10f81379a5789f
 | leq_1db81797fbf16ca5
 |  | X_2_2
 |  | const_9 = 9
 | leq_5c7fc875b1d46fe3
 |  | const_1 = 1
 |  | X_2_2

 and_cb393ffe746cf345
 | leq_58318b31d4f50cfb
 |  | X_3_2
 |  | const_9 = 9
 | leq_620d2c7d86f06f95
 |  | const_1 = 1
 |  | X_3_2

 and_dd7b3bf37f25acbe
 | leq_25f4212a99015bbe
 |  | X_4_2
 |  | const_9 = 9
 | leq_f0bd5fbae9ec0d70
 |  | const_1 = 1
 |  | X_4_2

 and_d035128e1f0f3bdd
 | leq_2ad9ea94c8cbd695
 |  | X_5_2
 |  | const_9 = 9
 | leq_accb06f57e2ba0d7
 |  | const_1 = 1
 |  | X_5_2

 and_f40d10db42ad3f6e
 | leq_8d5c6994f89b20c8
 |  | X_6_2
 |  | const_9 = 9
 | leq_a72d623d359fb293
 |  | const_1 = 1
 |  | X_6_2

 and_cce3b8e80f7941d3
 | leq_762f8c5e45b68735
 |  | const_1 = 1
 |  | X_7_2
 | leq_facefc358841f567
 |  | X_7_2
 |  | const_9 = 9

 and_6ea6ad8a62ea52c9
 | leq_2d79e65d2e87bf8e
 |  | X_8_2
 |  | const_9 = 9
 | leq_3aa43210f504d10
 |  | const_1 = 1
 |  | X_8_2

 and_ca24cbd3e601ab98
 | leq_49caf6b17fdb2237
 |  | X_9_2
 |  | const_9 = 9
 | leq_e77e5d38f9939a25
 |  | const_1 = 1
 |  | X_9_2

 and_fc4519dd76487a52
 | leq_4fdb0d673d4b8877
 |  | X_1_3
 |  | const_9 = 9
 | leq_b4749515cda17f3e
 |  | const_1 = 1
 |  | X_1_3

 ⋮
 eq_52962a4723ffe178
 | X_1_8
 | X_1_8

 eq_7631ad5a4db0ba8a
 | X_2_8
 | X_2_8

 eq_e3e3099959242eee
 | X_3_8
 | const_6 = 6

 eq_3f8b46db4ca8e04a
 | X_4_8
 | X_4_8

 eq_1d2bc36a587f8cce
 | X_5_8
 | X_5_8

 eq_5e486f2e84bdacdb
 | X_6_8
 | X_6_8

 eq_cefeb88a10768a1f
 | X_7_8
 | const_8 = 8

 eq_d1be9198106bf284
 | X_8_8
 | X_8_8

 eq_f84a5762fb991b6c
 | X_9_8
 | const_7 = 7

 eq_2d017e8e50553990
 | X_1_9
 | X_1_9

 eq_ebc64589fcc890cc
 | X_2_9
 | X_2_9

 eq_95f73805835f69cb
 | X_3_9
 | X_3_9

 eq_290cc45b1804d9df
 | X_4_9
 | const_3 = 3

 eq_8ae5b89d9de60fb9
 | X_5_9
 | const_1 = 1

 eq_1187474addf2ab2e
 | X_6_9
 | const_6 = 6

 eq_147e360d5715143b
 | X_7_9
 | X_7_9

 eq_40e977cc36265ac6
 | X_8_9
 | const_5 = 5

 eq_29b7b29789ac23ed
 | X_9_9
 | const_9 = 9
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
