push!(LOAD_PATH, "../src")
using Satisfiability

#=
 = Adapted from: https://avigad.github.io/lamr/using_smt_solvers.html#application-verification
 = 
 = This example shows how to use the Satisfiability.jl package to verify the
 = correctness of a popcount function. The popcount function counts the number
 = of 1s in a bit vector. 
 = 
 = The popcount function is implemented using a divide-and-conquer approach, 
 = which is a common technique for counting the number of 1s in a bit vector. 
 =
 = The popcount function is also implemented using a brute-force approach, 
 = which is a simple but inefficient way to count the number of 1s in a bit 
 = vector. The two implementations are then compared to verify that they are 
 = equivalent. 
 =#

# function pop_count()


@satvariable(x, BitVector, 32)   # Our input variable, x
@satvariable(x1, BitVector, 32)  # After the first, second and third lines
@satvariable(x2, BitVector, 32)
@satvariable(x3, BitVector, 32)

#= 
= METHOD 1: using a kind of 'divide and conquer' approach to sum up the 
= number of 1s in the bit vector x. This corresponds to the function:
= 
= function popcount(x::UInt32)::UInt32
=     x := x - ((x >> 1) & 0x55555555)
=     x := (x & 0x33333333) + ((x >> 2) & 0x33333333)
=     x := (((x + (x >> 4)) & 0x0f0f0f0f) * 0x01010101) >> 24
=     return x
= end
= 
= Note: we're using `>>>` for logical right shift.
=#

line_1 = x1 == x - ((x >>> 1) & 0x55555555)
line_2 = x2 == (x1 & 0x33333333) + ((x1 >>> 2) & 0x33333333)
line_3 = x3 == (((x2 + (x2 >>> 4)) & 0x0f0f0f0f) * 0x01010101) >>> 24

# METHOD 2: verify this is correct by extracting the bits from x, and summing
# them up. This is a brute-force method, but it is useful for verification.
extracted_bits = BitVectorExpr[
    ite(
        x[i] == bvconst(1, 1),
        bvconst(1, 32),
        bvconst(0, 32)
    )
    for i in 1:32
]

# We conjecture that the two methods are equivalent.
conjecture = and(line_1, line_2, line_3) ⟹ (sum(extracted_bits) == x3)

# Verify they're equivalent -- if !conjecture is UNSAT, then our conjecture is 
# always true, so the two methods are equivalent.
status = sat!(¬conjecture, solver=Z3())
println(status)
