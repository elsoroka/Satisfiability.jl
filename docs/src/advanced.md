# Advanced usage
```@contents
Pages = ["advanced.md"]
Depth = 3
```

Note: Some of the options described on this page require you to use the SMTLIB2 specification language directly.

### Custom solver options and using other solvers
To customize solver options or use a different (unsupported) solver, use the syntax

```julia
solver = Solver("My Solver", `program_name --option1 --option2`)
sat!(problem, solver=solver) # sat! will use your provided command to invoke the solver
```

The command you provide must launch a solver that accepts SMTLIB2-formatted commands and can respond to `(get-model)` in SAT mode. (An example of a command that does NOT work is `cvc5 --interactive`, because `CVC5` cannot answer `(get-model)` without the `--produce-models` option.)

To familiarize yourself with what this means, you may use `save` to generate a small SMT file for a satisfiable problem, then [call a solver from the terminal](installation.md#installing-a-solver), paste in the contents of your SMT file, and issue the command `(get-model)`. This is exactly what Satisfiability.jl does when you call  `sat!`. Armed with this knowledge, go forth and customize your solver command.

### Setting the solver logic
You can set the solver logic using an optional keyword argument in `sat!`.
The solver logic must be a string corresponding to a [valid SMT-LIB logic](http://smtlib.cs.uiowa.edu/logics.shtml). Users are responsible for selecting a logic that reflects the problem they intend to solve - Satisfiability.jl does not perform any correctness checking.

### Custom interactions using `send_command`
Satisfiability.jl provides an interface to issue SMT-LIB commands and receive SMT-LIB-formatted solver responses programmatically. This is useful if you wish to build your own decision logic or parser using advanced solver functionality.

If you just want to use an SMT solver interactively, for example by `push`ing or `pop`ping assertions, check out [Interactive Solving](interactive.md).

!!! note SMT-LIB solver modes.

In the SMT-LIB specification, after entering a problem and issuing the command `(check-sat)` the solver will be in either `sat` or `unsat` mode. The solver mode determines which commands are valid: for example, `(get-unsat-core)` is only valid in `unsat` mode and `(get-model)` is only valid in `sat` mode. You can find descriptions of modes and listings of valid commands in the latest [SMT-LIB Standard](http://www.smtlib.org/).

Here's an example.
```jldoctest; output = false
using Satisfiability
@satvariable(x[1:2], Bool)
expr = (x[1] ∧ ¬x[1]) ∧ or(x) # unsat

interactive_solver = open(Z3())

send_command(interactive_solver, "(set-option :produce-unsat-cores true)", dont_wait=true)

# smt() adds the command (check-sat), so Z3 will be in either `sat` or `unsat` mode after this command.
input = smt(expr)*"\n(check-sat)\n"
response = send_command(interactive_solver, input, is_done=is_sat_or_unsat)

println("status = $response") # "unsat"

response = send_command(interactive_solver, "(get-unsat-core)", is_done=nested_parens_match)
println(response)

# more interactions via `send_command`...

# it's good form to clean up your open solver process
close(interactive_solver)

# output

status = unsat

()
```

When using this functionality, you are responsible for keeping track of the solver mode and parsing the result of `send_command`. For convenience, `parse_model(model::String)` can parse the result of the SMT-LIB command `(get-model)`, returning a dictionary with variable names as keys and satisfying assignments as values.


**Checking if the response is complete**
Receiving a complete solver response is not as simple as it sounds, for two reasons.
1. The solver may take a long time to respond, for example when calling `(check-sat)`.
2. The solver's response may be large, thus it may be received in several chunks.

The `send_command` function has an optional argument `is_done` for checking whether the full response has been received. Two convenience functions are provided: `nested_parens_match(response::String)` returns `true` if `response` begins with `(` and ends with a matching `)`. This ensures the entire output is returned when issuing commands such as `(get-model)` where the entire response is wrapped in 1 set of parentheses. Many solver responses follow this format.
`is_sat_or_unsat` is very simple: if the response contains `sat` or `unsat` it returns `true`, otherwise it's `false`.

!!! warning Multiple parenthesized statements

If your command produces a response with multiple separate statements, for example `(statement_1)\n(statement_2)`, `nested_parens_match` is not guaranteed to return the entire response. The intended use case is `((statement_1)\n(statement_2))`. This should only happen if you issue two SMT-LIB commands at once.

**Customizing `is_done`**

A custom function `is_done(response::String)::Bool`, should have the following behavior:
* `is_done` returns `true` if the given `response` is valid (in whatever sense you define) and `false` if not.
* `send_command` will WAIT for more output while `is_done` is false.

SAT solvers can be slow and some commands produce long outputs. Without `is_done`, `send_command` could receive a partial response and prematurely return.

For full implementation details, please see the [source code](https://github.com/elsoroka/Satisfiability.jl/blob/main/src/call_solver.jl) of `call_solver.jl`.