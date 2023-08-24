##### CALLING A SAT SOLVER #####

include("call_solver.jl")

"""
    sat!(z::BoolExpr, Z3())
    sat!(z1, z2,..., CVC5())
    
Solve the SAT problem using a Solver. If the problem is satisfiable, update the values of all `BoolExprs` in `prob` with their satisfying assignments.

Possible return values are `:SAT`, `:UNSAT`, or `:ERROR`. `prob` is only modified to add Boolean values if the return value is `:SAT`.
By default, sat! will reset the values of expressions in `prob` to `nothing` if `prob` is unsatisfiable. To change this behavior use the keyword argument `clear_values_if_unsat`. For example,`sat!(prob, CVC5(), clear_values_if_unsat=false)`.

**Alternate usage:**

```julia
    io = open("some_file.smt")
    sat!(io::IO, solver::Solver)
````
In io mode, sat! reads the contents of the Julia IO object and passes them to the solver. Thus, users must ensure `read(io)` returns a complete and correct string of SMT-LIB commands, including `(check-sat)` or equivalent.
"""
function sat!(prob::BoolExpr, solver::Solver, clear_values_if_unsat=true)

    smt_problem = smt(prob)*"(check-sat)\n"
    status, values, interactive_solver = talk_to_solver(smt_problem, solver)
    
    # Only assign values if there are values. If status is :UNSAT or :ERROR, values will be an empty dict.
    if status == :SAT
        assign!(prob, values)
    elseif clear_values_if_unsat
        __clear_assignment!(prob)
    end
    # sat! doesn't return the process. To use the process, for example to interact or get an unsat proof, use the lower-level functions in call_solver.jl
    close(interactive_solver)
    return status
end

function sat!(io::IO, solver::Solver, clear_values_if_unsat=true)
    status, values, interactive_solver = talk_to_solver(read(io, String), solver)
    
    # sat! doesn't return the process. To use the process, for example to interact or get an unsat proof, use the lower-level functions in call_solver.jl
    close(interactive_solver)
    return status
end

sat!(zs::Vararg{Union{Array{T}, T}}; solver=Z3()) where T <: BoolExpr = length(zs) > 0 ?
                                                           sat!(__flatten_nested_exprs(all, zs...), solver) :
                                                           error("Cannot solve empty problem (no expressions).")

                                                           # this version accepts an array of exprs and [exprs] (arrays), for example sat!([z1, z2, z3])
sat!(zs::Array, solver::Solver) = sat!(zs...; solver=Solver)


##### INTERACTIVE SOLVING #####

# In this mode one works with an InteractiveSolver which is an open process to a solver
"""
    push(solver::InteractiveSolver, n::Integer)

Push n empty assertion levels onto the solver's assertion stack. Usually `push(1, solver)` is sufficient.
If n is 0, no assertion levels are pushed. This corresponds exactly to the SMT-LIB command `(push n)`.
"""
function push(solver::InteractiveSolver, n::Integer; is_done=(o::String)->true, timeout=0.002, line_ending=Sys.iswindows() ? "\r\n" : '\n')
    if n >= 0
        output = send_command(solver, "(push $n)", dont_wait=true, line_ending=line_ending)
        return output
    else
        error("Must push a nonnegative number of assertion levels.")
    end
end

"""
    pop(solver::InteractiveSolver, n::Integer)

Pop n empty assertion levels off the solver's assertion stack.
If n is 0, no assertion levels are pushed. This corresponds exactly to the SMT-LIB command `(pop n)`.
"""
function pop(solver::InteractiveSolver, n::Integer; is_done=(o::String)->true, timeout=0.002, line_ending=Sys.iswindows() ? "\r\n" : '\n')
    if n >= 0
        output = send_command(solver, "(pop $n)", dont_wait=true, line_ending=line_ending)
        return output
    else
        error("Must pop a nonnegative number of assertion levels.")
    end
end

function assert(solver::InteractiveSolver, exprs::Vararg{T}) where T <: BoolExpr

end

"""
    interactive_solver = open(Z3()) # open an InteractiveSolver process
    status, values = sat!(interactive_solver, exprs...) # check satisfiability of exprs

When working with an InteractiveSolver process, issues the `(check-sat)` command.
The optional `exprs`, if provided, will be asserted before `(check-sat)` is issued. This is equivalent to the SMT-LIB `(check-sat-assuming expr1, expr2,...)` command.

If no assertions have been made, sat! throws an error.

**Note that in this mode, sat! can only set the values of exprs provided in the function call**
That means if you `assert(expr1)` and then call `sat!(interactive_solver, expr2)`, `value(expr1)` will be `nothing` **even if the problem is SAT**. To alleviate this, `sat!` returns `(status, values)` where `values` is a Dict of variable names and satisfying assignments. To assign the values of `expr1`, call `assign!(values, expr1)`.
"""
function sat!(interactive_solver::InteractiveSolver, exprs::Array{T}; line_ending=Sys.iswindows() ? "\r\n" : '\n') where T <: BoolExpr
    # We cannot check sat if there are no assertions. The solver will be in the wrong mode.
    dict = Dict{String, Any}()
    if length(exprs) == 0
        # We have no exprs to assert, so we dig through command_history to make sure there are assertions that haven't been reset.
        # A case this does not catch is if you pop all the assertions. Honestly at some point we cannot protect the users from themselves anymore.
        last_assert = findlast((c) -> startswith(c, "(assert"),interactive_solver.command_history)
        last_reset = findlast((c) -> startswith(c, "(reset"),interactive_solver.command_history) # finds both reset and reset-assertions
        last_assert = isnothing(last_assert) ? -1 : last_assert
        last_reset = isnothing(last_reset) ? 0 : last_reset
        if last_reset > last_assert
            @error "Cannot check satisfiability, no assertions."
            return :ERROR, dict
        end
    end

    # Make the definitions in exprs
    for e in exprs
        commands = smt(e, assert=false, as_list=true)
        # This filters out previously defined statements.
        # For example, if we already sent (define-fun x () Bool), sending it again produces a solver error.
        to_send = filter((c) -> !(c in interactive_solver.command_history), commands)
        send_command(interactive_solver, to_send, line_ending=line_ending, dont_wait=true)
    end
    names = getproperty.(exprs, :name)

    # Now there's at least one assertion.
    output = send_command(interactive_solver, "(check-sat-assuming ($(join(names, " "))))", is_done=is_sat_or_unsat, line_ending=line_ending)
    status = :ERROR
    if strip(output) == "sat"
        output = send_command(interactive_solver, "(get-model)", is_done=nested_parens_match, line_ending=line_ending)
        dict = parse_model(output)
        map((e) -> assign!(e, dict), exprs)
        status = :SAT
    else
        status = :UNSAT
    end
    return status, dict
end

sat!(interactive_solver::InteractiveSolver, exprs::Vararg{T}; line_ending=Sys.iswindows() ? "\r\n" : '\n') where T <: BoolExpr = sat!(interactive_solver, collect(exprs), line_ending=line_ending)


"""
"""
function assert!(interactive_solver::InteractiveSolver, exprs::Array{T}; line_ending=Sys.iswindows() ? "\r\n" : '\n') where T <: BoolExpr
    for e in exprs
        commands = smt(e, assert=true, as_list=true)
        # This filters out previously defined statements.
        # For example, if we already sent (define-fun x () Bool), sending it again produces a solver error.
        to_send = filter((c) -> !(c in interactive_solver.command_history), commands)
        send_command(interactive_solver, to_send, line_ending=line_ending, dont_wait=true)
    end
end

assert!(solver::InteractiveSolver, exprs::Vararg{T}; line_ending=Sys.iswindows() ? "\r\n" : '\n') where T <: BoolExpr = assert!(solver, collect(exprs), line_ending=line_ending)
"""
    set_option(solver::InteractiveSolver, option, value)
    
    # for example,
    set_option(solver, "produce-assertions", true)
    set_option(solver, ":diagnostic-output-channel", "stderr")

Set a solver option. A list of options your solver may support can be found in [section 4.1.7 of the SMT-LIB standard](http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf).
Note that 

See `get_option` for notes on successfully receiving long or slow solver responses.
    """
function set_option!(solver::InteractiveSolver, option::String, value::Any; is_done=(o::String)->false, timeout=0.002, line_ending=Sys.iswindows() ? "\r\n" : '\n')
    output = send_command(solver, "(set-option :$option $value)", is_done=is_done, timeout=timeout, line_ending=line_ending)
    return output
end

"""
    get_option(solver::InteractiveSolver, option)

    # for example
    result = get_option(solver, "produce-assertions")

Get the current value of a solver option. A list of options your solver may support can be found in [section 4.1.7 of the SMT-LIB standard](http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf).

If you have difficulty receiving a solver response, the keyword arguments timeout and is_done are provided.
timeout is a Float64 specifying the number of seconds to wait for the response.
is_done is a function. is_done(s::String) returns `true` if the output is complete and `false` otherwise.
This is primarily used to receive long responses which may arrive in several chunks. If you expect the output of your command to be wrapped in a single set of parentheses, use the provided function `nested_parens_match` for output checking.
"""
function get_option(solver::InteractiveSolver, option::String; is_done=(o::String)->false, timeout=0.002, line_ending=Sys.iswindows() ? "\r\n" : '\n')
    output = send_command(solver, "(get-option :$option)", is_done=is_done, timeout=timeout, line_ending=line_ending)
    return output
end

"""
    reset!(solver::InteractiveSolver)

Resets the solver to its state when first opened. See [section 4.2.1](http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf) of the SMT-LIB standard.
"""
reset!(solver::InteractiveSolver) = send_command(solver, "(reset)", dont_wait=true)

"""
    reset_assertions!(solver::InteractiveSolver)

Removes all assertions, popping n levels off the solver's assertion stack. After this command, the stack will be at level 1 and there will be no assertions set. See [section 4.2.1](http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf) of the SMT-LIB standard.
"""
reset_assertions!(solver::InteractiveSolver) = send_command(solver, "(reset-assertions)", dont_wait=true)

##### ASSIGNMENTS ####
# see discussion on why this is the way it is
# https://docs.julialang.org/en/v1/manual/performance-tips/#The-dangers-of-abusing-multiple-dispatch-(aka,-more-on-types-with-values-as-parameters)
# https://groups.google.com/forum/#!msg/julia-users/jUMu9A3QKQQ/qjgVWr7vAwAJ

__julia_symbolic_ops = Dict(
    :eq      => ==,
    :add     => +,
    :sub     => -,
    :mul     => *,
    :div     => /,
    :neg     => -,
    :lt      => <,
    :leq     => <=,
    :geq     => >=,
    :gt      => >,
    :bv2int  => Int,
)
# This is the default function for propagating the values back up in __assign! (called when a problem is sat and a satisfying assignment is found).
# This function should be specialized as necessary.
function __propagate_value!(z::AbstractExpr)
    op = z.op ∈ keys(__julia_symbolic_ops) ? __julia_symbolic_ops[z.op] : eval(z.op)
    vs = getproperty.(z.children, :value)
    if length(vs)>1
        z.value = op(vs...)
    else
        z.value = op(vs[1])
    end
end

"""
    assign!(e::AbstractExpr, assignment::Dict)

Assigns the values of expressions in e (including nested expressions and variables) using `assignment`, a Dict where every key is a string corresponding to an expression name, and the corresponding value is its satisfying assignment.

`assign!` is intended to be useful in two cases.
1. Using an `assignment` dict returned by `sat!` in interactive mode.This looks like:

```julia
    # define some exprs
    interactive_solver = open(solver)
    assert(interactive_solver, exprs...)
    status, assignment = sat!(interactive_solver)
    assign!.(exprs, assignment)
```
2. Using an `assignment` dict returned by `parse_model`, which parses the raw SMT-LIB output of "(get-model)".
"""
function assign!(z::T, assignment::Dict) where T <: AbstractExpr
    if z.op == :identity
        if z.name ∈ keys(assignment)
            z.value = assignment[z.name]
        else
            @warn "Value not found for variable $(z.name)."
            z.value = missing # this is better than nothing because & and | automatically skip it (three-valued logic).
        end
    elseif z.op == :const
        ; # const already has .value set so do nothing
    else
        if any(ismissing.(map( (z) -> assign!(z, assignment), z.children)))        
            z.value = missing
        else
            __propagate_value!(z)
        end
    end
    return z.value
end

function __clear_assignment!(z::AbstractExpr)
    z.value = nothing
    if length(z.children) > 0
        map(__clear_assignment!, z.children)
    end
end