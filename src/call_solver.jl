##### SOLVER OBJECT #####
struct Solver
    name::String
    cmd::Cmd
    options::Dict{String, Any}
end

# some instantiation options
Solver(name::String, cmd::Cmd) = Solver(name, cmd, Dict{String, Any}())
if Sys.iswindows()
    Z3() = Solver("Z3", `z3.exe -smt2 -in`, Dict{String, Any}())
    cvc5() = Solver("cvc5", `cvc5.exe --interactive --produce-models`, Dict{String, Any}())
else
    Z3() = Solver("Z3", `z3 -smt2 -in`, Dict{String, Any}())
    cvc5() = Solver("cvc5", `cvc5 --interactive --produce-models`, Dict{String, Any}())
end

##### INVOKE AND TALK TO SOLVER #####

# __wait_for_result attempts to accumulate output from pstdout until is_done is true
function __wait_for_result(pstdout::Base.Pipe, is_done; sleeptime=0.002)
    output = ""
    while true
        new_bytes = String(readavailable(pstdout))
        output = output*new_bytes
        if is_done(output)
            return output
        end
        sleep(sleeptime)
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
    send_command(pstdin::Base.Pipe, pstdout::Base.Pipe, cmd::String; is_done=nested_parens_match, timeout=Inf)

Open a solver in a new process with in, out, and err pipes.
Uses Base.process. Check the source code to see the exact implementation.
"""
function send_command(pstdin::Base.Pipe, pstdout::Base.Pipe, cmd::String; is_done = f(output::String) = false, line_ending='\n')
    # f() is required because Task can only schedule functions with no inputs
    f() = __wait_for_result(pstdout, is_done)
    t = Task(f)
    schedule(t)
    # now send the command
    write(pstdin, cmd*line_ending) # in case the input is missing a line ending

    output = fetch(t) # throws automatically if t fails
    return output
end

"""
    proc, pstdin, pstdout, pstderr = open_solver(s::Solver)

Open a solver in a new process with in, out, and err pipes.
Uses Base.process. Check the source code to see the exact implementation.
"""
function open_solver(s::Solver)
    pstdin = Pipe()
    pstdout = Pipe()
    pstderr = Pipe()
    proc = run(pipeline(s.cmd,
                        stdin = pstdin, stdout = pstdout, stderr = pstderr),
                        wait = false)
    if process_exited(proc)
        @error "Unable to start solver with command $(s.cmd)."
    end
    return proc, pstdin, pstdout, pstderr
end


function talk_to_solver(input::String, s::Solver)
    line_ending = Sys.iswindows() ? "\r\n" : '\n'
    proc, pstdin, pstdout, pstderr = open_solver(s)

    is_sat_or_unsat(output) = occursin("sat", output)
    output = send_command(pstdin, pstdout, input, is_done=is_sat_or_unsat, line_ending=line_ending)

    @debug "Solver output for (check-sat):$line_ending\"$output\""
    if length(output) == 0
        @error "Unable to retrieve solver output."
        return :ERROR, Dict{String, Bool}(), proc

    elseif process_exited(proc)
        @error "Solver crashed on input! Please file a bug report."
        return :ERROR, Dict{String, Bool}(), proc
    end
    original_output = deepcopy(output)
    output = filter(isletter, output)
    if output == "unsat" # the problem was successfully given to Z3, but it is UNSAT
        return :UNSAT, Dict{String, Bool}(), proc

    elseif output == "sat" # the problem is satisfiable
        output = send_command(pstdin, pstdout, "(get-model)$line_ending", is_done=nested_parens_match, line_ending=line_ending)
        @debug "Solver output for (get-model):$line_ending\"$output\""

        satisfying_assignment = parse_smt_output(output)
        return :SAT, satisfying_assignment, proc

    else
        @error "Solver error:$line_ending $(original_output)"
        return :ERROR, Dict{String, Bool}(), proc
    end
end
