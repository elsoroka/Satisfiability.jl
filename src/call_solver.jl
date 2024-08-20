import Base.open, Base.close
using z3_jll

##### SOLVER OBJECT #####
abstract type AbstractSolver end

struct Solver <: AbstractSolver
    name::String
    cmd::Cmd
    options::Dict{String, Any}
end

##### INTERACTIVE SOLVER #####
# This is an open process
mutable struct InteractiveSolver <: AbstractSolver
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
Z3(; kwargs...) = Solver("Z3", `$(z3()) -smt2 -in`, kwargs)
if Sys.iswindows()
    try success(`z3.exe --version`)
        # use z3 if it is available on path
        Z3(; kwargs...) = Solver("Z3", `z3.exe -smt2 -in`, kwargs)
    catch
    end
    CVC5(; kwargs...) = Solver("CVC5", `cvc5.exe --interactive --produce-models --incremental`, kwargs)
    Yices(; kwargs...) = Solver("Yices", `yices-smt2.exe --interactive --smt2-model-format`)
else
    try success(`z3.exe --version`)
        # use z3 if it is available on path
        Z3(; kwargs...) = Solver("Z3", `z3 -smt2 -in`, kwargs)
    catch
    end
    CVC5(; kwargs...) = Solver("CVC5", `cvc5 --interactive --produce-models --incremental`, kwargs)
    Yices(; kwargs...) = Solver("Yices", `yices-smt2 --interactive --smt2-model-format`)
end

##### INVOKE AND TALK TO SOLVER #####

# __wait_for_result attempts to accumulate output from pstdout until is_done is true
function __wait_for_result(pstdout::Base.Pipe, is_done; sleeptime=0.02, timeout=Inf)
    output = ""
    line_ending = Sys.iswindows() ? "\r\n" : '\n'
    time_elapsed = 0.0
    # IO DRAMA https://discourse.julialang.org/t/avoiding-readavailable-when-communicating-with-long-lived-external-program/61611/20
    # IO DRAMA https://github.com/JuliaLang/julia/issues/24526
    # GET YOUR IO DRAMA HERE https://github.com/JuliaLang/julia/issues/24717
    # The summary of the IO drama is that readavailable can block.
    # We cannot check bytesavailable because on some systems the OS level buffer hides the bytesavailable. Thus, bytesavailable returns 0 even when pstdout has bytes
    # There is currently NO way to read the buffered bytes from a Pipe in a non-blocking manner. This may be related to issue #24717, pipe async-ness
    # This is why we have to timeout in send_command which waits for __wait_for_result.
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
    is_sat_or_unsat(output::String)

Return true if output contains "sat" or "unsat".
"""
is_sat_or_unsat(output) = occursin("sat", output)

"""
    send_command(pstdin::Base.Pipe, pstdout::Base.Pipe, cmd::String; is_done=nested_parens_match, timeout=Inf, line_ending='\n')

Open a solver in a new process with in, out, and err pipes.
Uses Base.process. Check the source code to see the exact implementation.
"""
function send_command(solver::InteractiveSolver, cmd::Union{Array{S}, S}; is_done = f(output::String) = true, timeout=Inf, line_ending='\n', dont_wait=false) where S <: String
    if isa(cmd, String)
        push!(solver.command_history, strip.(split(cmd, line_ending, keepempty=false))...)
    else
        push!(solver.command_history, strip.(cmd)...)
        cmd = join(cmd, line_ending) # batch them for writing
    end
    
    if dont_wait
        @debug "Sending command: $cmd$line_ending"
        write(solver.pstdin, cmd*line_ending) # in case the input is missing a line ending
        return nothing
    else
        # f() is required because Task can only schedule functions with no inputs
        f() = __wait_for_result(solver.pstdout, is_done, timeout=timeout)
        t = Task(f)
        schedule(t)
        @debug "Sending command: $cmd$line_ending"
        # now send the command
        write(solver.pstdin, cmd*line_ending) # in case the input is missing a line ending
        # DO NOT PLACE ANYTHING HERE. It may throw off the timing.
        output = fetch(t) # throws automatically if t fails
        @debug "Response: $output"
        return output
    end
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
    isolver = InteractiveSolver(s.name, s.cmd, s.options, pstdin, pstdout, pstderr, proc, String[])
    send_command(isolver, "(set-option :print-success false)", dont_wait=true) # mandatory configuration step to not break the parser
    return isolver
end

"""
    close(s::InteractiveSolver)

Close an InteractiveSolver, cleaning up and terminating its processes and pipes.
"""
function close(s::InteractiveSolver)
    send_command(s, "(exit)", dont_wait=true)
    close(s.pstdin)
    close(s.pstdout)
    close(s.pstderr)
    close(s.proc)
end


# This function opens the interactive_solver and solves the problem. It's used by sat!. It shouldn't really be used by users.
function talk_to_solver(input::String, s::Solver)
    line_ending = Sys.iswindows() ? "\r\n" : '\n'
    interactive_solver = open(s)

    output = send_command(interactive_solver, input, is_done=is_sat_or_unsat, line_ending=line_ending)

    @debug "Solver output for (check-sat):$line_ending\"$output\""
    if length(output) == 0
        @error "Unable to retrieve solver output."
        close(interactive_solver)
        return :ERROR, Dict{String, Bool}()

    elseif process_exited(interactive_solver.proc)
        @error "Solver crashed on input! Please file a bug report."
        close(interactive_solver)
        return :ERROR, Dict{String, Bool}()
    end
    original_output = deepcopy(output)
    output = filter(isletter, output)
    if output == "unsat" # the problem was successfully given to Z3, but it is UNSAT
        close(interactive_solver)
        return :UNSAT, Dict{String, Bool}()

    elseif output == "sat" # the problem is satisfiable
        output = send_command(interactive_solver, "(get-model)$line_ending", is_done=nested_parens_match, line_ending=line_ending)
        @debug "Solver output for (get-model):$line_ending\"$output\""

        satisfying_assignment = parse_model(output)
        close(interactive_solver)
        return :SAT, satisfying_assignment

    else
        @error "Solver error:$line_ending $(original_output)"
        close(interactive_solver)
        return :ERROR, Dict{String, Bool}()
    end
end
