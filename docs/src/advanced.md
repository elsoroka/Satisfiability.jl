# Advanced usage
```@contents
Pages = ["advanced.md"]
Depth = 3
```

NOTE: Some of the options described on this page require you to use the SMTLIB2 specification language directly.

### Custom solver options and using other solvers
To customize solver options or use a different (unsupported) solver, use the syntax

```julia
solver = Solver("My Solver", `program_name --option1 --option2`)
sat!(problem, solver) # sat! will use your provided command to invoke the solver
```

The command you provide must launch a solver that accepts SMTLIB2-formatted commands and can respond to `(get-model)` in SAT mode. (An example of a command that does NOT work is `cvc5 --interactive`, because `cvc5` cannot answer `(get-model)` without the `--produce-models` option.)

To familiarize yourself with what this means, you may use `save` to generate a small SMT file for a satisfiable problem, then [call a solver from the terminal](installation.md#installing-a-solver), paste in the contents of your SMT file, and issue the command `(get-model)`. This is exactly what BooleanSatisfiability.jl does when you call  `sat!`. Armed with this knowledge, go forth and customize your solver command.

### Custom interactions with solvers
BooleanSatisfiability provides an interface to issue SMT2 commands and receive SMT2-formatted solver responses programmatically. This is useful if you wish to build your own decision logic or parser using advanced solver functionality.

!!! note SMT2 solver modes.
In the SMT2 specification, after entering a problem and issuing the command `(check-sat)` the solver will be in either `sat` or `unsat` mode. The solver mode determines which commands are valid: for example, `(get-unsat-core)` is only valid in `unsat` mode and `(get-model)` is only valid in `sat` mode. You can find descriptions of modes and listings of valid commands in the latest [SMT-LIB Standard](http://www.smtlib.org/).

Here's an example.
```julia
@satvariable(x[1:2], Bool)
expr = (x[1] ∧ ¬x[1]) ∧ any(x) # unsat

solver = Z3()
proc, pstdin, pstdout, pstderr = open_process(solver)

# smt() adds the command (check-sat), so Z3 will be in either `sat` or `unsat` mode after this command.
input = smt(expr)
response = send_command(pstdin, pstdout, input, is_done=nested_parens_match)

println("status = $response") # :UNSAT

response = send_command(pstdin, pstdout, "(get-unsat-core)", is_done=nested_parens_match)
println(response)

# more interactions via `send_command`...

# it's good form to clean up your process
close(proc)
```

When using this functionality, you are responsible for keeping track of the solver mode and parsing the result of `send_command`.

**Checking if the response is complete**

The `send_command` function has an optional argument `is_done` for checking whether the full response has been received. The default is `nested_parens_match(output::String)` which returns `true` if `response` contains at least 1 matching pair of parentheses. This ensures the entire output is returned when issuing commands such as `(get-model)` where the response is wrapped in at least 1 set of parentheses.

!!! warning Multiple parenthesized statements
If your command produces a response with multiple separate statements, for example `(statement_1)\n(statement_2)`, `nested_parens_match` is not guaranteed to return the entire response. The intended use case is `((statement_1)\n(statement_2))`.

**Customizing `is_done`**

A custom function `is_done(response::String)::Bool`, should have the following behavior:
* `is_done` returns `true` if the given `response` is valid (in whatever sense you define) and `false` if not.
* `send_command` will WAIT for more output while `is_done` is false.

SAT solvers can be slow and some commands produce long outputs. Without `is_done`, `send_command` could receive a partial response and prematurely return.

For full implementation details, please see the [source code](https://github.com/elsoroka/BooleanSatisfiability.jl/blob/main/src/call_solver.jl) of `call_solver.jl`.