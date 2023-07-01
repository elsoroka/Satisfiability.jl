# Finding a meeting time
We have n people's availabilities for the meeting times 9a, 10a, 11a, 12, 1p, 2p, 3p, 4p. Each person's availability is reprsented as a Boolean vector ``a^\top\in \{0,1\}^8``.
We would like to schedule ``J`` meetings between different groups of people, represented by ``J`` index sets ``\mathcal{I_j}\subseteq\{1,\dots,n\}``.


Rules:
* Each meeting ``\mathcal{I}_j`` must occur at one time ``t``.
* All people attending meeting ``\mathcal{I}_j`` must be available at time ``t``.
* All people attending meeting ``\mathcal{I}_j`` must not be attending another meeting at time ``t``.
* No attendee should have >2 hours of consecutive meetings.

### Setup
We concatenate the availability row vectors into a 5 x 8 Boolean matrix ``\bar A``.
```@example
using BooleanSatisfiability

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

# A is a matrix-valued variable such that ``A_{it} = 1`` if attendee ``i`` is in a meeting at time ``t`` and 0 otherwise.
A = Bool(n,T,"A")
```
The `index_sets` represent which meeting attendees are required at each meeting ``\mathcal{I_j}``.
```@example
index_sets = [[1,2,3], [3,4,5], [1,3,5], [1,4]]
J = length(index_sets) # number of meetings
```

### Logical constraints
If attendee ``i`` is unavailable at time ``t`` (``\bar A_{it} = 0``) then they cannot be in a meeting at time ``t``.
```@example
unavailability = and(¬A_bar .⟹ ¬A)
```

For each meeting ``j``, all attendees in index set ``\mathcal{I_j}`` must be available at some time ``t`` and not attending another meeting.
```@example
M = [and(A[index_sets[j], t]) for j=1:J, t=1:T]

# get a list of conflicts
conflicts = [filter((i) -> i != j && length(intersect(index_sets[j], index_sets[i])) > 0, 1:J) for j=1:J ]
no_double_booking = all([M[j,t] ⟹ ¬or(M[conflicts[j],t]) for j=1:J, t=1:T])
```

All meetings must be scheduled.
```@example
require_one_time = all([or(M[j,:]) for j=1:J])
```
No attendee should have more than 2 consecutive hours of meetings.
```@example
time_limit = all([¬and(A[i,t:t+2]) for i=1:n, t=1:T-2])
```

### Solving the problem
```@example
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
```