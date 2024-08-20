
# Job shop scheduling

The job shop scheduling problem is a linear integer problem arising in operations research.

Suppose you are managing a machine shop with several different jobs in progress.
Each job consists of a series of tasks. Some of the tasks have ordering constraints: e.g. parts must be manufactured before they can be installed in a larger assembly.
Due to equipment constraints, we cannot schedule two tasks requiring the same machine at the same time. Additionally, all tasks must have a worker assigned to complete them.

In this problem ([from Microsoft's Z3 tutorial](https://microsoft.github.io/z3guide/docs/theories/Arithmetic/)) we have three jobs, each consisting of one task to be completed first by worker A and one to be completed second by worker B. Each task has an integer-valued duration. Workers cannot work on two tasks at once or take each others' tasks.

We'd like to find a solution such that all three jobs can be completed in an 8-hour workday.

* Define two vector-valued variables t1 and t2 such that tj[i] is the start time of job i for worker j.

* Define two vector-valued variables d1 and d2 such that dj[i] is the duration of job i for worker j.

```jldoctest label4; output = false
using Satisfiability
n = 3 # number of jobs
m = 2 # number of tasks per job
@satvariable(t1[1:n], Int)
@satvariable(t2[1:n], Int)
d1 = [2; 3; 2]
d2 = [1; 1; 3]

# output

3-element Vector{Int64}:
 1
 1
 3
```
A start time of 0 corresponds to the first hour of the workday, and an end time of 8 corresponds to the last hour of the workday.
```jldoctest label4; output = false
working_hours = and(and.(t1 .>= 0, t2 .+ d2 .<= 8))

# output

and_8088c809b835015f
 | geq_2cddece62a748b44
 |  | t1_1
 |  | const_0 = 0
 | geq_964fa3ba70096779
 |  | t1_2
 |  | const_0 = 0
 | geq_b232da16892553c5
 |  | t1_3
 |  | const_0 = 0
 | leq_1b855e8b7bb05b23
 |  | add_9cb3dafa858c9030
 |  |  | const_1 = 1
 |  |  | t2_2
 |  | const_8 = 8
 | leq_d50a28ba3057fbc1
 |  | add_998ad3f6b518c087
 |  |  | const_1 = 1
 |  |  | t2_1
 |  | const_8 = 8
 | leq_e7ce3611a480214c
 |  | add_4580cc9b2c8bdd52
 |  |  | const_3 = 3
 |  |  | t2_3
 |  | const_8 = 8
```

Sequencing constraint: For each job, A must complete the first task before B can start the second task
```jldoctest label4; output = false
sequencing = and(t2 .>= t1 .+ d1)

# output

and_a18c8b7108359cf1
 | geq_539cad1e0b93b56f
 |  | t2_3
 |  | add_1e74cdf94378d61b
 |  |  | const_2 = 2
 |  |  | t1_3
 | geq_a62c1462891b1648
 |  | t2_2
 |  | add_545b00bfa7d73eb6
 |  |  | const_3 = 3
 |  |  | t1_2
 | geq_c71b8039639696d7
 |  | t2_1
 |  | add_4a9919f7c9a68e8d
 |  |  | const_2 = 2
 |  |  | t1_1
```

Overlap constraint between all permutations
```jldoctest label4; output = false
overlaps = [(1,2), (1,3), (2,3)]
overlap_1 = and(or( t1[i] >= t1[j] + d1[j], t1[j] >= t1[i] + d1[i]) for (i,j) in overlaps)
overlap_2 = and(or( t2[i] >= t2[j] + d2[j], t2[j] >= t2[i] + d2[i]) for (i,j) in overlaps)

# output
and_838c8b1a32177263
 | or_12b107ef977da744
 |  | geq_655589726cc21ac5
 |  |  | t2_1
 |  |  | add_9cb3dafa858c9030
 |  |  |  | const_1 = 1
 |  |  |  | t2_2
 |  | geq_c5e38efbef81c979
 |  |  | t2_2
 |  |  | add_998ad3f6b518c087
 |  |  |  | const_1 = 1
 |  |  |  | t2_1
 | or_239a278a4ab06849
 |  | geq_16aa900b991be6a0
 |  |  | t2_3
 |  |  | add_998ad3f6b518c087
 |  |  |  | const_1 = 1
 |  |  |  | t2_1
 |  | geq_464e3994de72767c
 |  |  | t2_1
 |  |  | add_4580cc9b2c8bdd52
 |  |  |  | const_3 = 3
 |  |  |  | t2_3
 | or_f6e831b5814141fc
 |  | geq_cca5ea12ec4608ee
 |  |  | t2_2
 |  |  | add_4580cc9b2c8bdd52
 |  |  |  | const_3 = 3
 |  |  |  | t2_3
 |  | geq_f4f3db3e981b1090
 |  |  | t2_3
 |  |  | add_9cb3dafa858c9030
 |  |  |  | const_1 = 1
 |  |  |  | t2_2
```

Solve the problem
```jldoctest label4; output = false
status = sat!(working_hours, sequencing, overlap_1, overlap_2, solver=Z3())
println("status = $status")
if status == :SAT
    println("t1 = $(value(t1))")
    println("t2 = $(value(t2))")
end

# output

status = SAT
t1 = [0, 4, 2]
t2 = [2, 7, 4]
```