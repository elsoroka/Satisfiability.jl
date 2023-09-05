# NOTE THAT THIS FILE IS SET UP TO BE RUN FROM examples/paper_examples
push!(LOAD_PATH, "../../src/")
using Satisfiability, BenchmarkTools
using StatsBase, Random
Random.seed!(97)


# A classic problem in graph theory is figuring out how to color nodes of a graph such that no two adjacent nodes have the same color.
# In this example we time a graph coloring task using interactive solving.
# The goal is to find up to a fixed number of colorings for a randomly generated graph of size n with n links

# returns a list of nodes and a list of edges as tuples
function make_graph(n::Integer, n_edges=div(n*3, 2))
    A = collect(Iterators.product(1:n, 1:n))
    pairs = cat([A[i, i+1:n] for i=1:n]..., dims=1)
    edges = sample(pairs, Weights(ones(length(pairs))), min(length(pairs), n_edges), replace=false)
    return 1:n, edges
end

function graph_coloring(n::Int, edges, n_to_find=3, limit=3, solutions=Array)
    @satvariable(nodes[1:n], Int)
    limits = and.(nodes .>= 1, nodes .<= limit)

    connections = cat([distinct(nodes[i], nodes[j]) for (i,j) in edges], dims=1)

    open(Z3()) do interactive_solver
        # make assertion # add "(set-logic QF_LIA)\n"
        send_command(interactive_solver, "(set-logic QF_LIA)", dont_wait=true)
        assert!(interactive_solver, limits, connections)
        i = 1
        while i <= n_to_find
            # Try to solve the problem
            status, assignment = sat!(interactive_solver)
            if status == :SAT
                assign!(nodes, assignment)
                solutions[i,:] .= value(nodes)
                #println("i = $i, status = $status, assignment = $assignment")
                # Use assert! to exclude the solution we just found.
                assert!(interactive_solver, not(and(nodes .== value(nodes))))
            else
                #println("unsat!")
                break
            end
            i += 1
        end
    end
    return solutions
end

# solutions is a list of list of values, where each one is progressively excluded
function make_smt_file(n::Int, edges, limit=4, solutions=Array)
    @satvariable(nodes[1:n], Int)
    limits = and.(nodes .>= 1, nodes .<= limit)

    connections = cat([distinct(nodes[i], nodes[j]) for (i,j) in edges], dims=1)
    
    outfile = open("graph_genfiles/graph_coloring_gen_$n.smt", "w+")
    write(outfile,"(set-logic QF_LIA)\n")
    write(outfile, smt(limits, connections, assert=true))
    write(outfile, "(check-sat)\n(get-model)\n")

    for solution in eachrow(solutions)
        if !all(solution .== 0) # if they're 0 no solution is in this row
            #println(solution)
            write(outfile, smt(not(and(nodes .== solution)), assert=true, as_list=true)[end])
            write(outfile, "\n(check-sat)\n(get-model)\n")
        end
    end
    close(outfile)
end

function run_with_timing!(cmd::Cmd)
    # Why do this? run(cmd, wait=true) throws ERROR on a nonzero exitcode
    # but I want to use the exitcode to determine whether z3 completed or timed out.
    result = run(cmd, wait=false)
    wait(result)
    return result.exitcode
end


# Timing

to_find=5 # find up to this many solutions

# Cause precompilation
s = zeros(to_find, 4)
_,edges = make_graph(4)
graph_coloring(4, edges, to_find, 1, s)
make_smt_file(4, edges, 1, s)
result = run_with_timing!(`timeout 20m z3 -smt2 graph_genfiles/graph_coloring_gen_4.smt`)
println("got $s in precompilation")

open("graph_execution_log_$(time()).txt", "w") do graph_execution_log

    # Print for reproducibility.
    versioninfo(graph_execution_log)
    githash = strip(read(`git show -s --format=%H`, String))
    gitbranch = strip(read(`git rev-parse --abbrev-ref HEAD`, String))
    write(graph_execution_log, "\nSatisfiability.jl on branch $gitbranch, commit hash $githash\n,Finding $to_find solutions per n.")

    satjl_timing = Array{Union{Missing, Float64}}(undef, 20)
    fill!(satjl_timing, missing)
    z3_timing = Array{Union{Missing, Float64}}(undef, 20)
    fill!(satjl_timing, missing)
    filegen_timing = Array{Union{Missing, Float64}}(undef, 20)
    fill!(filegen_timing, missing)

    write(graph_execution_log, "n,sat_timing (seconds),z3_timing (seconds),filegen (seconds)\n")
    println("n,sat_timing (seconds),z3_timing (seconds),filegen (seconds)\n")
    
    samples = [10; 10; 10; 10; 5; 5; 5; ones(Int, 12)]
    for i=4:16
        n = 2^i
        solutions=zeros(Int, to_find, n)

        n_edges = i <= 6 ? div(3*n, 2) : 2*n # number of edges should ensure there are solutions, otherwise it's not quite a fair comparison
        _, edges = make_graph(n, n_edges)
        b1 = @benchmarkable graph_coloring($n, $edges, $to_find, 3, $solutions) samples=samples[i]
        t = run(b1)
        satjl_timing[i] = mean(t).time*1e-9 # the 1e-9 converts the time to seconds
        
        b2 = @benchmarkable make_smt_file($n, $edges, 3, $solutions) samples=1
        t = run(b2)
        filegen_timing[i] = mean(t).time*1e-9 

        cmd = `timeout 20m z3 -smt2 graph_genfiles/graph_coloring_gen_$n.smt`
        b3 = @benchmarkable run_with_timing!($cmd) samples=samples[i]
        t = run(b3)
        z3_timing[i] = mean(t).time*1e-9 

        write(graph_execution_log, "$n,$(satjl_timing[i]),$(z3_timing[i]),$(filegen_timing[i])\n" )
        println("$n $(satjl_timing[i]) $(z3_timing[i]) $(filegen_timing[i])")
    end
end