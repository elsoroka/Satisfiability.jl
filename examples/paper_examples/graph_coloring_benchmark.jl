# NOTE THAT THIS FILE IS SET UP TO BE RUN FROM examples/paper_examples
push!(LOAD_PATH, "../../src/")
using Satisfiability, BenchmarkTools


# A classic problem in graph theory is figuring out how to color nodes of a graph such that no two adjacent nodes have the same color.
# In this example we time a graph coloring task using interactive solving.
# The goal is to find a certain number of solutions for a prism graph (https://mathworld.wolfram.com/PrismGraph.html) of size n.

function graph_coloring(n::Int, n_to_find=3, limit=4, solutions=Array)
    @satvariable(nodes[1:2*n], Int)
    inner = nodes[1:n]
    outer = nodes[n+1:end]

    limits = and.(nodes .>= 1, nodes .<= limit)

    connections = cat([distinct(inner[i], inner[i+1]) for i=1:n-1],
                      [distinct(outer[i], outer[i+1]) for i=1:n-1],
                      [distinct(inner[end], inner[1]), distinct(outer[end], outer[1])],
                      [distinct(inner[i], outer[i]) for i=1:n], dims=1)

    open(Z3()) do interactive_solver
        # make assertion # add "(set-logic QF_LIA)\n"
        assert!(interactive_solver, limits, connections)
        i = 1
        while i <= n_to_find
            # Try to solve the problem
            status, assignment = sat!(interactive_solver)
            if status != :SAT
                error("Something went wrong!")
            end
            assign!(nodes, assignment)
            solutions[i,:] .= value(nodes)
            #println("i = $i, status = $status, assignment = $assignment")
            # Use assert! to exclude the solution we just found.
            assert!(interactive_solver, not(and(nodes .== value(nodes))))
            i += 1
        end
    end
    return solutions
end

# solutions is a list of list of values, where each one is progressively excluded
function make_smt_file(n::Int, solutions::Array, limit=4)

    # We construct this of size n https://en.wikipedia.org/wiki/Prism_graph
    @satvariable(nodes[1:2*n], Int)
    inner = nodes[1:n]
    outer = nodes[n+1:end]

    limits = and.(nodes .>= 1, nodes .<= limit)

    connections = cat([distinct(inner[i], inner[i+1]) for i=1:n-1],
                      [distinct(outer[i], outer[i+1]) for i=1:n-1],
                      [distinct(inner[end], inner[1]), distinct(outer[end], outer[1])],
                      [distinct(inner[i], outer[i]) for i=1:n], dims=1)
    
    outfile = open("graph_genfiles/graph_coloring_gen_$n.smt", "w+")
    write(outfile,"(set-logic QF_LIA)\n")
    write(outfile, smt(limits, connections, assert=true))
    write(outfile, "(check-sat)\n(get-model)\n")

    for solution in eachrow(solutions)
        #println(solution)
        write(outfile, smt(not(and(nodes .== solution)), assert=true, as_list=true)[end])
        write(outfile, "\n(check-sat)\n(get-model)\n")
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

to_find=3 # find 3 solutions

# Cause precompilation
s = zeros(to_find, 3*2)
graph_coloring(3, to_find, 4, s)
make_smt_file(3, s, 4)
result = run_with_timing!(`timeout 20m z3 -smt2 graph_genfiles/graph_coloring_gen_2.smt`)
println("got $s")

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

    write(graph_execution_log, "n,sat_timing (seconds),z3_timing (seconds)\n")
    

    for i=3:20
        solutions=zeros(Int, to_find, 2*i)
        b1 = @benchmarkable graph_coloring($i, $to_find, 4, $solutions) samples=10
        t = run(b1)
        satjl_timing[i] = mean(t).time*1e-9 # the 1e-9 converts the time to seconds
        
        make_smt_file(i, solutions, 4)

        cmd = `timeout 20m z3 -smt2 graph_genfiles/graph_coloring_gen_$i.smt`
        b2 = @benchmarkable run_with_timing!($cmd) samples=10
        t = run(b2)
        z3_timing[i] = mean(t).time*1e-9 

        write(graph_execution_log, "$i,$(satjl_timing[i]),$(z3_timing[i])\n" )
        println("$i $(satjl_timing[i]) $(z3_timing[i])")
    end
end