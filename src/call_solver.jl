##### INVOKE AND TALK TO SOLVER #####

function talk_to_solver(input::String, cmd)
    pstdin = Pipe()
    pstdout = Pipe()
    pstderr = Pipe()
    proc = run(pipeline(cmd,
                        stdin = pstdin, stdout = pstdout, stderr = pstderr),
                        wait = false)
    
    if process_exited(proc)
        @error "Unable to start solver with command $cmd."
        return :ERROR, Dict{String, Bool}(), proc
    end

    function get_result()
        output = ""
        stack = 0
        while true
            new_bytes = String(readavailable(pstdout))
            stack += length(filter( (c) -> c == '(', new_bytes)) - length(filter( (c) -> c == ')', new_bytes))
            output = output*new_bytes
            if length(new_bytes) > 0 && stack == 0
                return output
            end
            sleep(0.002)
        end
    end
    t = Task(get_result)
    schedule(t)

    # now we have a pipe open that we can communicate to z3 with
    write(pstdin, input)
    write(pstdin, "\n") # in case the input is missing \n
    
    output = fetch(t) # throws automatically if t fails
    @debug "Solver output for (check-sat):\n\"$output\""
    if length(output) == 0
        @error "Unable to retrieve solver output."
        return :ERROR, Dict{String, Bool}(), proc

    elseif process_exited(proc)
        @error "Solver crashed on input! Please file a bug report."
        return :ERROR, Dict{String, Bool}(), proc
    end

    if startswith(output, "unsat") # the problem was successfully given to Z3, but it is UNSAT
        return :UNSAT, Dict{String, Bool}(), proc

    elseif startswith(output, "sat") # the problem is satisfiable
        t = Task(get_result)
        schedule(t)
    
        write(pstdin, "(get-model)\n")
        output = fetch(t) # throws automatically if t fails
        @debug "Solver output for (get-model):\n\"$output\""

        satisfying_assignment = parse_smt_output(output)
        return :SAT, satisfying_assignment, proc

    else
        @error "Solver error:\n$(output)"
        return :ERROR, Dict{String, Bool}(), proc
    end
end
