# NOTE THAT THIS FILE IS SET UP TO BE RUN FROM examples/paper_examples
using Pkg
Pkg.add("BenchmarkTools")
Pkg.add("Satisfiability")
Pkg.add("Plots")
using Satisfiability, BenchmarkTools, Plots, InteractiveUtils # for versioninfo()

# https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_LIA/-/tree/master/pidgeons
# The pigeon-hole benchmarks are Linear Integer Arithmetic benchmarks
# pertaining to fitting pigeons in holes. They are all unsat, because the pigeons do not fit.
# We chose them because the SMT-LIB file, while readable, is very long due to the single-variable syntax of SMT-LIB

# The following code generates a pigeon-hole benchmark of size n.

# The assertion pattern is that
#p[1,1] + P[1,2] >= 1
#p[2,1] + p[2,2] >= 1
#p[3,1] + p[3,2] >= 1
#p[1,1] + p[2,1] + p[3,1] <= 1
#p[1,2] + p[2,2] + p[3,2] <= 1
# That is, each row p[i,:] >= 1
# and each column p[:,j] <= 1


function pigeonhole(n::Int)
    CLEAR_VARNAMES!() # this clears our "dict" of SMT varnames, which is used to warn about duplicates
    
    @satvariable(P[1:n+1, 1:n], Int)
    each_row = BoolExpr[sum(P[i,:]) >= 1 for i=1:n+1]
    each_col = BoolExpr[sum(P[:,j]) <= 1 for j=1:n]

    # Also, P should be in {1,0}.
    bounds = and.(P .>= 0, P .<= 1)
    status = sat!(each_row, each_col, bounds, solver=Z3(), start_commands="(set-logic QF_LIA)")
    if status != :UNSAT
        @error("Something went wrong!")
    end
end

function run_with_timing!(cmd::Cmd)
    # Why do this? run(cmd, wait=true) throws ERROR on a nonzero exitcode
    # but I want to use the exitcode to determine whether z3 completed or timed out.
    result = run(cmd, wait=false)
    wait(result)
    return result.exitcode
end

# This function generates our own pigeonhole smt files.
# We'll use it in case minor differences in the smt file changes the speed of the solver.
function pigeonhole_smt_files(n::Int)
    CLEAR_VARNAMES!() # this clears our "dict" of SMT varnames, which is used to warn about duplicates
    
    @satvariable(P[1:n+1, 1:n], Int)
    each_row = BoolExpr[sum(P[i,:]) >= 1 for i=1:n+1]
    each_col = BoolExpr[sum(P[:,j]) <= 1 for j=1:n]
    bounds = and.(P .>= 0, P .<= 1)
    open("pigeons_genfiles/pigeonhole_gen_$n.smt", "w") do outfile
        save(each_row, each_col, bounds, io=outfile, start_commands="(set-logic QF_LIA)")
    end
end

# Preallocate arrays
z3_exitcode = Array{Union{Missing, Int64}}(undef, 20)
fill!(z3_exitcode, missing)
z3_timing = Array{Union{Missing, Float64}}(undef, 20)
fill!(z3_timing, missing)
satjl_timing = Array{Union{Missing, Float64}}(undef, 20)
fill!(satjl_timing, missing)
filegen_timing = Array{Union{Missing, Float64}}(undef, 20)
fill!(filegen_timing, missing)

nmax = 11 # times out after 11

open("pigeons_execution_log_$(time()).txt", "w") do pigeons_execution_log
    # Print for reproducibility.
    versioninfo(pigeons_execution_log)

    # First we time generating SMT files
    
    # cause precompilation
    pigeonhole_smt_files(2)
    
    write(pigeons_execution_log, "Generating SMT files\nsize,time(seconds)\n")
    for n=2:nmax
        t = @elapsed pigeonhole_smt_files(n)
        filegen_timing[n] = t
        write(pigeons_execution_log, "$n,$t\n")
    end
    write(pigeons_execution_log, "Generated SMT files.\n")
    println("Generated SMT files.")

    # First we establish a baseline by timing Z3 as a command line process.
    write(pigeons_execution_log, "\nSolver-on-command-line baseline\nSolver,command,time(seconds),exitcode\n")

    # Cause precompilation
    cmd1 = `timeout 20m z3 -smt2 pigeons_genfiles/pigeonhole_gen_2.smt`
    z3_exitcode[1] = run_with_timing!(cmd1)

    for i=2:nmax
        #cmd = `timeout 20m z3 -smt2 QF_LIA-master-pidgeons/pidgeons/pigeon-hole-$i.smt2`
        cmd = `timeout 20m z3 -smt2 pigeons_genfiles/pigeonhole_gen_$i.smt`
        z3_timing[i] = @elapsed z3_exitcode[i] = run_with_timing!(cmd)
        write(pigeons_execution_log, "z3,$cmd,$(z3_timing[i]),$(z3_exitcode[i])\n")
        println(z3_timing[i], z3_exitcode[i])
    end
    

    # Now we time Satisfiability.jl!

    # cause precompilation
    pigeonhole(2)

    # Assumption: Since Satisfiability.jl cannot possibly make z3 any faster, we only need to time the benchmarks that didn't time out for z3

    # Get some reproducibility information
    githash = strip(read(`git show -s --format=%H`, String))
    gitbranch = strip(read(`git rev-parse --abbrev-ref HEAD`, String))

    write(pigeons_execution_log, "\nSatisfiability.jl on branch $gitbranch, commit hash $githash\nsize,time(ms)\n")

    nsamples = [10; 10; 10; 10; 10; 10; 5; 5; 5; 5; ones(10)]
    for i=2:nmax
        if !ismissing(z3_timing[i]) && z3_timing[i] <= 1200
            b = @benchmarkable pigeonhole($i) samples=nsamples[i]
            t = run(b)
            satjl_timing[i] = mean(t).time*1e-9 # the 1e-9 converts the time to seconds
            write(pigeons_execution_log, "$i,$(satjl_timing[i])\n")
            println(satjl_timing[i])
        end
    end

end

##### PLOTTING #####
# Note that the paper plots are generated using pgfplots but to simplify the Docker artifact we will generate the same plots in Julia Plots.jl.
# They may look a bit different.

ns = collect(2:nmax)
p1 = plot(ns, satjl_timing[2:nmax], label="Satisfiability.jl", color=:green, marker=:square,
          yaxis=:log,
          xlabel="Benchmark size", ylabel="Time (seconds)", size=(400,400))
p1 = plot!(p1, ns, z3_timing[2:nmax], label="Z3", color=:blue, marker=:o)
p2 = plot(ns, 100.0 .* satjl_timing[2:nmax] ./ z3_timing[2:nmax], color=:blue, marker=:o,
          xaxis=:log, ylims=(50,150), primary=false,
          xlabel="Benchmark size", ylabel="% of Z3 solve time", size=(400,400))

p = plot(p1, p2, size=(800,400))
savefig(p, "pigeons.pdf")

# save the time to write the files
outfile = open("linecount_time_pigeon.txt", "w")
write(outfile, "linecount,seconds\n")
for i=2:nmax
    # count the number of lines in the generated file
    tmp = read(`wc -l pigeons_genfiles/pigeonhole_gen_$i.smt`, String)
    line_count = parse(Int, split(tmp, limit=2)[1])
    write(outfile, "$line_count,$(filegen_timing[i])\n")
end
close(outfile)