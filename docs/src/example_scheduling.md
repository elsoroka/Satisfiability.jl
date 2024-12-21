# Finding a meeting time
We have the availabilities of `n` people for the meeting times `9a`, `10a`, `11a`, `12`, `1p`, `2p`, `3p`, `4p`. Each person's availability is represented as a Boolean vector ``a^\top\in \{0,1\}^8``.
We would like to schedule ``J`` meetings between different groups of people, represented by ``J`` index sets ``\mathcal{I_j}\subseteq\{1,\dots,n\}``.

# Rules
* Each meeting ``\mathcal{I}_j`` must be scheduled at exactly one time ``t``.
* All attendees of meeting ``\mathcal{I}_j`` must be available at the scheduled time ``t``.
* No attendee of ``\mathcal{I}_j`` can participate in another meeting scheduled at the same time ``t``.
* No attendee should have more than two consecutive hours of meetings.

### Setup
We concatenate the availability row vectors into a `5 × 8` Boolean matrix ``\bar A``.
```jldoctest label5; output = false
using Satisfiability

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
@satvariable(A[1:n, 1:T], Bool)
println(size(A))

# output

(5, 8)
```
The `index_sets` represent which meeting attendees are required at each meeting ``\mathcal{I_j}``.
```jldoctest label5; output = false
index_sets = [[1,2,3], [3,4,5], [1,3,5], [1,4]]
J = length(index_sets) # number of meetings

# output

4
```

### Logical constraints
If attendee ``i`` is unavailable at time ``t`` (``\bar A_{it} = 0``) then they cannot be in a meeting at time ``t``.
```jldoctest label5; output = false
unavailability = and(¬A_bar .⟹ ¬A)

# output

and_e22650cf96be44e6
 | not_1bac913b12a338bc
 |  | A_2_5
 | not_2262b4a859b33800
 |  | A_2_7
 | not_384097f73d28f91
 |  | A_3_4
 | not_547e26f28fb4c097
 |  | A_2_6
 | not_569a776aa6467d1c
 |  | A_4_7
 | not_5c95bf02c25d8a4a
 |  | A_5_1
 | not_60b022ebd3fc95e0
 |  | A_3_7
 | not_65ebb7bfd84897b7
 |  | A_4_3
 | not_71aac0f717453642
 |  | A_1_2
 | not_826349772eba559b
 |  | A_2_4
 | not_9aacfd0327980298
 |  | A_5_6
 | not_aa6196e5d4cc26af
 |  | A_1_4
 | not_b0741e715f7a7528
 |  | A_5_5
 | not_bf350ccb950b79ac
 |  | A_4_6
 | not_cf2c14a0b2535f8
 |  | A_2_1
 | not_d5f0d95ec3b95bec
 |  | A_5_7
 | not_d9bf741be6fa2852
 |  | A_4_8
```

For each meeting ``j``, all attendees in the index set ``\mathcal{I_j}`` must be available at some time ``t`` and not attend another meeting.
```jldoctest label5; output = false
M = [and(A[index_sets[j], t]) for j=1:J, t=1:T]

# get a list of conflicts
conflicts = [filter((i) -> i != j && length(intersect(index_sets[j], index_sets[i])) > 0, 1:J) for j=1:J ]
no_double_booking = and(M[j,t] ⟹ ¬or(M[conflicts[j],t]) for j=1:J, t=1:T)
println("Constructed $(length(no_double_booking.children)) double-booking constraints.")

# output

Constructed 32 double-booking constraints.
```

All meetings must be scheduled.
```jldoctest label5; output = false
require_one_time = and(or(M[j,:]) for j=1:J)
println("Constructed $(length(require_one_time.children)) one-time constraints.")

# output

Constructed 4 one-time constraints.
```
No attendee should have more than 2 consecutive hours of meetings.
```jldoctest label5; output = false
time_limit = and(¬and(A[i,t:t+2]) for i=1:n, t=1:T-2)
println("Constructed $(length(time_limit.children)) consecutivity constraints.")

# output

Constructed 30 consecutivity constraints.
```

### Solving the problem
```jldoctest label5; output = false
# solve
exprs = [no_double_booking, require_one_time, unavailability, time_limit]
status = sat!(exprs, solver=Z3())

println("status = $status") # for this example we know it's SAT
times = ["9a", "10a", "11a", "12p", "1p", "2p", "3p", "4p"]
for j=1:J
    Mj_value = value(M[j,:])
    println("Meeting with attendees $(index_sets[j]) can occur at $(times[filter((i) -> Mj_value[i], 1:length(Mj_value))]) .== true)])")
end

println("Value A: $(value(A))")
println("Value N: $(value(M))")

# output

status = SAT
Meeting with attendees [1, 2, 3] can occur at ["11a"] .== true)])
Meeting with attendees [3, 4, 5] can occur at ["10a"] .== true)])
Meeting with attendees [1, 3, 5] can occur at ["4p"] .== true)])
Meeting with attendees [1, 4] can occur at ["9a", "1p"] .== true)])
Value A: Bool[1 0 1 0 1 0 0 1; 0 0 1 0 0 0 0 0; 0 1 1 0 0 0 0 1; 1 1 0 0 1 0 0 0; 0 1 0 0 0 0 0 1]
Value N: Bool[0 0 1 0 0 0 0 0; 0 1 0 0 0 0 0 0; 0 0 0 0 0 0 0 1; 1 0 0 0 1 0 0 0]
```
