# Advanced usage
```@contents
Pages = ["advanced.md"]
Depth = 3
```

NOTE: Some of the options described on this page will suggest that you use the low-level SMTLIB2 specification language directly.

### Custom solver options and using other solvers
To customize solver options or use a different (unsupported) solver, see (TODO). The command you provide must launch a solver that accepts SMTLIB2-formatted commands and can respond to `(get-model)` in SAT mode. (An example of a command that does NOT work is `cvc5 --interactive --`, because `cvc5` cannot produce models without the `--produce-models` option.)

To familiarize yourself with what this means, you may use `save` to generate a small SMT file for a satisfiable problem, then invoke the solver of your choice, paste in the contents of your SMT file and issue the command `(get-model)`. This is exactly what BooleanSatisfiability.jl does when you call  `sat!`. Armed with this knowledge, you may now go forth and customize your solver command.

### Custom interactions with solvers
BooleanSatisfiability exposes a low-level interface to issue SMT commands and receive SMT-formatted solver output programmatically. This is useful if you wish to build your own decision logic or parser using advanced solver functionality.

To use this interface, you should understand solver modes as defined in the SMTLIB2 specification. Specifically, you should know that after entering a problem and issuing the command `(check-sat)` (the SMTLIB2 version of `sat!`), the solver will be in either `sat` or `unsat` mode depending on the result. The solver mode determines which commands are valid. You can find descriptions of modes and listings of valid commands in the latest *SMT-LIB Standard*.

Here's an example of what this might look like.
```julia
@Variable(x[1:2], :Bool)
expr = (x[1] ∧ ¬x[1]) ∧ any(x) # unsat

solver = Z3()
proc = open_process(solver)
result = sat!(expr, process=proc) # sat! issues the command (check-sat), so Z3 will be in either `sat` or `unsat` mode after this line.
println("status = $result") # :UNSAT

result = send_command(proc, "(get-unsat-core)", is_valid=nested_parens_match, timeout=10)
println(result) # you're responsible for interpreting this string
# additional interactions via `send_command` may follow
# it's good form to clean up your process
close(proc)
```

When using this functionality, you are responsible for keeping track of the solver mode and parsing the result of `send_command`.

**The `is_valid` function**

One `is_valid` function is provided: `nested_parens_match(output::String)`. This function returns True if `output` contains at least 1 matching pair of parentheses. This provides the appropriate behavior when issuing commands such as `(get-model)` where the expected output comes wrapped in at least 1 set of parentheses.

If you define a custom function `is_valid(output::String)::Bool`, it should have the following behavior:
* `is_valid` returns `true` if the given `output` is valid (in whatever sense you define) and `false` if not.
* `send_command` will WAIT for more output while `is_valid` is false and `timeout` seconds have not passed. If you set the `timeout` too short, you may receive truncated or no output.

This behavior is necessary because SAT solvers can be slow and some commands produce long outputs. Without this checking behavior `send_command` could receive partial output and prematurely return, missing the rest.

For full implementation details, please see the (source code)[https://github.com/elsoroka/BooleanSatisfiability.jl/blob/main/src/call_solver.jl] of `call_solver.jl`.