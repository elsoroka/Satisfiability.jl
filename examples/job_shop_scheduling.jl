push!(LOAD_PATH,"../src/")
using BooleanSatisfiability

# From https://microsoft.github.io/z3guide/docs/theories/Arithmetic/
# Job shop scheduling problem is a linear integer problem arising in operations research.
# Suppose you are managing a machine shop with several different jobs in progress.
# Each job consists of a series of tasks. Some of the tasks have ordering constraints: e.g. parts must be manufactured before they can be installed in a larger assembly.
# Due to equipment constraints, you cannot schedule two tasks requiring the same machine at the same time.
# Additionally, all tasks must have a worker assigned to complete them.

# In this problem we have three jobs, each consisting of one task to be completed first by worker A and one to be completed next by worker B.
# Each task has an integer-valued duration. Workers cannot work on two tasks at once or take each others' tasks.
# We'd like to find a solution such that all three jobs can be completed in an 8-hour workday.
# Define two vector-valued variables t1 and t2 such that tj[i] is the start time of job i for worker j.
# Define two vector-valued variables d1 and d2 such that dj[i] is the duration of job i for worker j.

n = 3 # number of jobs
m = 2 # number of tasks per job
@satvariable(t1[1:n], :Int)
@satvariable(t2[1:n], :Int)
d1 = [2; 3; 2]
d2 = [1; 1; 3]

# A start time of 0 corresponds to the first hour of the workday, and an end time of 8 corresponds to the last hour of the workday.
working_hours = all(and.(t1 .>= 0, t2 .+ d2 .<= 8))

# Sequencing constraint: For each job, A must complete the first task before B can start the second task
sequencing = and(t2 .>= t1 .+ d1)

# Overlap constraint between all permutations
overlaps = [(1,2), (1,3), (2,3)]
overlap_1 = all([or( t1[i] >= t1[j] + d1[j], t1[j] >= t1[i] + d1[i]) for (i,j) in overlaps])
overlap_2 = all([or( t2[i] >= t2[j] + d2[j], t2[j] >= t2[i] + d2[i]) for (i,j) in overlaps])

status = sat!(working_hours, sequencing, overlap_1, overlap_2, solver=Z3())
println("status = $status")
if status == :SAT
    println("t1 = $(value(t1))")
    println("t2 = $(value(t2))")
end