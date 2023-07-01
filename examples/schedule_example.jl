push!(LOAD_PATH,"../src/")
using BooleanSatisfiability

#= SCHEDULING TASK
We have n people's availabilities for 9a, 10a, 11a, 12, 1p, 2p, 3p, 4p defined as a vector of 0 and 1's
We would like to schedule $J$ meetings between different groups of people, represented by $J$ index sets $\mathcal{I_j}\subseteq\{1,\dots,n\}$.

Rules:
* Each meeting $\mathcal{I}_j$ must occur at one time $t$
* All people attending meeting $\mathcal{I}_j$ must be available at time $t$
* All people attending meeting $\mathcal{I}_j$ must not be attending another meeting at time $t$
* No attendee should have >2 hours of consecutive meetings.
=#

n = 5 # number of people
T = 8 # number of times

# nxT matrix: each row is one attendee's meeting availability
A_bar = Bool[
    1 0 1 0 1 1 1 1
    0 1 1 0 0 0 0 1
    1 1 1 0 1 1 0 1
    1 1 0 1 1 0 0 0
    0 1 1 1 0 0 0 1
]
index_sets = [[1,2,3], [3,4,5], [1,3,5], [1,4]]
J = length(index_sets) # number of meetings

A = Bool(n,T,"A")
unavailability = and(¬A_bar .⟹ ¬A)

M = [and(A[index_sets[j], t]) for j=1:J, t=1:T]

# for each meeting j, everyone must be available at some time t and not attending another meeting
# get a list of conflicts
conflicts = [filter((i) -> i != j && length(intersect(index_sets[j], index_sets[i])) > 0, 1:J) for j=1:J ]
no_double_booking = all([M[j,t] ⟹ ¬or(M[conflicts[j],t]) for j=1:J, t=1:T])

# all meetings must be scheduled
require_one_time = all([or(M[j,:]) for j=1:J])

# nobody should have more than 2 consecutive hours of meetings
time_limit = all([¬and(A[i,t:t+2]) for i=1:n, t=1:T-2])

# solve
exprs = [no_double_booking, require_one_time, unavailability, time_limit]
status = sat!(exprs)

println("status = $status") # for this example we know it's SAT
times = ["9a", "10a", "11a", "12p", "1p", "2p", "3p", "4p"]
for j=1:J
    println("Meeting with attendees $(index_sets[j]) can occur at $(times[findall(value(M[j,:]) .== true)])")
end

println("Value A: $(value(A))")
println("Value N: $(value(M))")