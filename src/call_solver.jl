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

    # now we have a pipe open that we can communicate to z3 with
    write(pstdin, input)
    write(pstdin, "\n") # in case the input is missing \n
    
    # read only the bytes in the buffer, otherwise it hangs
    output = String(readavailable(pstdout))

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
        write(pstdin, "(get-model)\n")
        sleep(0.01) # IDK WHY WE NEED THIS BUT IF WE DON'T HAVE IT, pstdout HAS 0 BYTES BUFFERED 
        # This has something to do with z3 and we need to fix it more correctly.
        output = String(readavailable(pstdout))
        satisfying_assignment = parse_smt_output(output)
        return :SAT, satisfying_assignment, proc

    else
        @error "Solver error:\n$(output)"
        return :ERROR, Dict{String, Bool}(), proc
    end
end