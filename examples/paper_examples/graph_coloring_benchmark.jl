# NOTE THAT THIS FILE IS SET UP TO BE RUN FROM examples/paper_examples
using Pkg;
Pkg.add("BenchmarkTools")
Pkg.add("Satisfiability")
Pkg.add("StatsBase")
Pkg.add("Plots")
Pkg.add("ArgParse")
using Satisfiability, BenchmarkTools
using StatsBase, Random, Plots, ArgParse, InteractiveUtils # for versioninfo()
Random.seed!(97)

s = ArgParseSettings()
@add_arg_table! s begin
    "--size", "-n"
    help = "Max size n"
    arg_type = Int
    default = 12 # times out at higher sizes
end

parsed_args = parse_args(ARGS, s)
nmax = parsed_args["size"]
println("Running up to size $nmax")

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
println("finished precompilation")

satjl_timing = Array{Union{Missing, Float64}}(undef, 20)
fill!(satjl_timing, missing)
z3_timing = Array{Union{Missing, Float64}}(undef, 20)
fill!(satjl_timing, missing)
filegen_timing = Array{Union{Missing, Float64}}(undef, 20)
fill!(filegen_timing, missing)

open("graph_execution_log_$(time()).txt", "w") do graph_execution_log

    # Print for reproducibility.
    versioninfo(graph_execution_log)
    githash = strip(read(`git show -s --format=%H`, String))
    gitbranch = strip(read(`git rev-parse --abbrev-ref HEAD`, String))
    write(graph_execution_log, "\nSatisfiability.jl on branch $gitbranch, commit hash $githash\n,Finding $to_find solutions per n.")

    write(graph_execution_log, "n,sat_timing (seconds),z3_timing (seconds),filegen (seconds)\n")
    println("n, sat_timing (seconds), z3_timing (seconds), filegen (seconds)\n")
    
    samples = [10; 10; 10; 10; 5; 5; 5; ones(Int, 13)]
    for i=4:nmax # sizes above 2^12 time out after 20 minutes
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
        println("$n, $(satjl_timing[i]), $(z3_timing[i]), $(filegen_timing[i])")
    end
end

##### PLOTTING #####
# Note that the paper plots are generated using pgfplots but to simplify the Docker artifact we will generate the same plots in Julia Plots.jl.
# They may look a bit different.

ns = 2.0.^(4:nmax)
p1 = plot(ns, satjl_timing[4:nmax], label="Satisfiability.jl", color=:green, marker=:square,
          xaxis=:log, yaxis=:log,
          xlabel="Benchmark size", ylabel="Time (seconds)", size=(400,400))
p1 = plot!(p1, ns, z3_timing[4:nmax], label="Z3", color=:blue, marker=:o)
p2 = plot(ns, 100.0 .* satjl_timing[4:nmax] ./ z3_timing[4:nmax], color=:blue, marker=:o,
          xaxis=:log, primary=false,
          xlabel="Benchmark size", ylabel="% of Z3 solve time", size=(400,400))

p = plot(p1, p2, size=(800,400))
savefig(p, "graph_coloring.pdf")

# save the time to write the files
outfile = open("linecount_time_graph.txt", "w")
write(outfile, "linecount,seconds\n")
for i=4:nmax
    n = 2^i
    # count the number of lines in the generated file
    tmp = read(`wc -l graph_genfiles/graph_coloring_gen_$n.smt`, String)
    line_count = parse(Int, split(tmp, limit=2)[1])
    write(outfile, "$line_count,$(filegen_timing[i])\n")
end
close(outfile)

