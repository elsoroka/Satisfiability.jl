import Base.open, Base.close

##### SOLVER OBJECT #####
abstract type AbstractSolver end

struct Solver <: AbstractSolver
    name::String
    cmd::Cmd
    options::Dict{String, Any}
end

##### INTERACTIVE SOLVER #####
# This is an open process
struct InteractiveSolver <: AbstractSolver
    name::String
    cmd::Cmd
    options::Dict{String, Any}
    pstdin::Pipe
    pstdout::Pipe
    pstderr::Pipe
    proc::Base.Process
    command_history::Array{String}
end


# some instantiation options, currently we are not using kwargs
Solver(name::String, cmd::Cmd; kwargs...) = Solver(name, cmd, kwargs)
if Sys.iswindows()
    Z3(; kwargs...) = Solver("Z3", `z3.exe -smt2 -in`, kwargs)
    CVC5(; kwargs...) = Solver("CVC5", `cvc5.exe --interactive --produce-models`, kwargs)
else
    Z3(; kwargs...) = Solver("Z3", `z3 -smt2 -in`, kwargs)
    CVC5(; kwargs...) = Solver("CVC5", `cvc5 --interactive --produce-models`, kwargs)
end

##### INVOKE AND TALK TO SOLVER #####

# __wait_for_result attempts to accumulate output from pstdout until is_done is true
function __wait_for_result(pstdout::Base.Pipe, is_done; sleeptime=0.002, timeout=Inf)
    output = ""
    time_elapsed = 0.0
    while true
        new_bytes = String(readavailable(pstdout))
        output = output*new_bytes
        if is_done(output) || time_elapsed > timeout
            return output
        end
        sleep(sleeptime)
        time_elapsed += sleeptime
    end
end

"""
    nested_parens_match(output::String)

Return true if output has > 0 length and an equal number of left ( and right ), which can be 0.
"""
function nested_parens_match(output::String)
    stack = length(filter( (c) -> c == '(', output)) - length(filter( (c) -> c == ')', output))
    return length(output) > 0 && stack == 0
end

"""
    send_command(pstdin::Base.Pipe, pstdout::Base.Pipe, cmd::String; is_done=nested_parens_match, timeout=Inf, line_ending='\n')

Open a solver in a new process with in, out, and err pipes.
Uses Base.process. Check the source code to see the exact implementation.
"""
function send_command(solver::InteractiveSolver, cmd::String; is_done = f(output::String) = false, timeout=Inf, line_ending='\n')
    # f() is required because Task can only schedule functions with no inputs
    f() = __wait_for_result(solver.pstdout, is_done, timeout=timeout)
    t = Task(f)
    schedule(t)
    push!(solver.command_history, split(cmd, line_ending, keepempty=false)...)

    # now send the command
    write(solver.pstdin, cmd*line_ending) # in case the input is missing a line ending
    # DO NOT PLACE ANYTHING HERE. It may throw off the timing.
    output = fetch(t) # throws automatically if t fails
    return output
end

"""
    interactive_solver = open(s::Solver)

Open a solver in a new process with in, out, and err pipes.
Uses Base.process. Check the source code to see the exact implementation.
"""
function open(s::Solver)
    pstdin = Pipe()
    pstdout = Pipe()
    pstderr = Pipe()
    proc = run(pipeline(s.cmd,
                        stdin = pstdin, stdout = pstdout, stderr = pstderr),
                        wait = false)
    if process_exited(proc)
        @error "Unable to start solver with command $(s.cmd)."
    end
    return InteractiveSolver(s.name, s.cmd, s.options, pstdin, pstdout, pstderr, proc, String[])
end

function close(s::InteractiveSolver)
    close(s.proc)
    close(s.pstdin)
    close(s.pstdout)
    close(s.pstderr)
end


# This function opens the interactive_solver and solves the problem. It's used by sat!. It shouldn't really be used by users.
function talk_to_solver(input::String, s::Solver)
    line_ending = Sys.iswindows() ? "\r\n" : '\n'
    interactive_solver = open(s)

    is_sat_or_unsat(output) = occursin("sat", output)
    output = send_command(interactive_solver, input, is_done=is_sat_or_unsat, line_ending=line_ending)

    @debug "Solver output for (check-sat):$line_ending\"$output\""
    if length(output) == 0
        @error "Unable to retrieve solver output."
        return :ERROR, Dict{String, Bool}(), interactive_solver

    elseif process_exited(interactive_solver.proc)
        @error "Solver crashed on input! Please file a bug report."
        return :ERROR, Dict{String, Bool}(), interactive_solver
    end
    original_output = deepcopy(output)
    output = filter(isletter, output)
    if output == "unsat" # the problem was successfully given to Z3, but it is UNSAT
        return :UNSAT, Dict{String, Bool}(), interactive_solver

    elseif output == "sat" # the problem is satisfiable
        output = send_command(interactive_solver, "(get-model)$line_ending", is_done=nested_parens_match, line_ending=line_ending)
        @debug "Solver output for (get-model):$line_ending\"$output\""

        satisfying_assignment = parse_smt_output(output)
        return :SAT, satisfying_assignment, interactive_solver

    else
        @error "Solver error:$line_ending $(original_output)"
        return :ERROR, Dict{String, Bool}(), interactive_solver
    end
end
