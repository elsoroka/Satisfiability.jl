using BooleanSatisfiability
#using LinearAlgebra, Plots

n = 3 # number of people
T = 2 # number of times
# nxT matrix: each row is one attendee's meeting availability
A_bar = [
    1 1
    0 1
    1 0
]
index_sets = [[1,2], [1,3]]#, [1,3,5]]#, [3,4]]
J = length(index_sets) # number of meetings

A = Bool(n,T,"A")
#=
#past_availability = all(¬A_bar .⟹ ¬A)
booked = BoolExpr[]
for i=1:n
    for t=1:T
        if A_bar[i,t]==0
            push!(booked, ¬A[i,t])
        end
    end
end
unavailability = all(booked)
=#

M = [and(A[index_sets[j], t]) for j=1:J, t=1:T]
#M = A[1:2,1:2]
# get a list
conflicts = [filter((i) -> i != j && length(intersect(index_sets[j], index_sets[i])) > 0, 1:J) for j=1:J ]
inner = [M[j,t] ⟹ ¬or(M[conflicts[j],t]) for j=1:J, t=1:T]

# for each meeting j, everyone must be available at some time t and not attending another meeting
meetings = [or(inner[j,:]) for j=1:J]

# nobody should have more than 2 consecutive hours of meetings
#time_limit = all([¬and(A[i,t:t+2]) for i=1:n, t=1:T-2])

# solve
exprs = [all(inner)]#, unavailability, time_limit]
status = sat!(exprs)
println("status = $status")
println("A = $(value(A))")