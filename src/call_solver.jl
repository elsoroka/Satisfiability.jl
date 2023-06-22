##### INVOKE AND TALK TO SOLVER #####

function talk_to_solver(input::String)
    cmd = `z3 -smt2 -in`
    pstdin = Pipe()
    pstdout = Pipe()
    pstderr = Pipe()
    proc = run(pipeline(cmd,
                        stdin = pstdin, stdout = pstdout, stderr = pstderr),
                        wait = false)
    # now we have a pipe open that we can communicate to z3 with
    write(pstdin, input)
    write(pstdin, "\n") # in case the input is missing \n
    
    # read only the bytes in the buffer, otherwise it hangs
    output = String(readavailable(pstdout))
    
    if length(output) == 0 # this shouldn't happen, but I put this check in otherwise it will hang waiting to read
        @error "Unable to retrieve input from z3 (this should never happen)."
        return :ERROR, Dict{String, Bool}(), proc
    end

    if startswith(output, "unsat") # the problem was successfully given to Z3, but it is UNSAT
        return :UNSAT, Dict{String, Bool}(), proc

    elseif startswith(output, "sat") # the problem is satisfiable
        write(pstdin, "(get-model)\n")
        sleep(0.001) # IDK WHY WE NEED THIS BUT IF WE DON'T HAVE IT, pstdout HAS 0 BYTES BUFFERED 
        output = String(readavailable(pstdout))
        satisfying_assignment = __parse_smt_output(output)
        return :SAT, satisfying_assignment, proc

    else
        @error "Z3 encountered the error: $(output)"
        return :ERROR, Dict{String, Bool}(), proc
    end
end