# Advanced usage
```@contents
Pages = ["advanced.md"]
Depth = 3
```

!!! note Some of the options described on this page require you to use the [SMTLIB2](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2024-09-20.pdf) specification language directly.

## Custom solver options and using other solvers (Experimental)
In theory, you can call any [SMTLIB2](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2024-09-20.pdf) compliant solver using its **interactive** command-line interface. In practice, this can be tricky and this feature is considered experimental.

To customize solver options or use a different (unsupported) solver, use the syntax

```julia
solver = Solver("My Solver", `program_name --option1 --option2`)
sat!(problem, solver=solver) # sat! will use your provided command to invoke the solver
```

The command you provide must launch a solver that accepts [SMTLIB2](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2024-09-20.pdf)-formatted commands and can respond to `(get-model)` in SAT mode. (An example of a command that does NOT work is `cvc5 --interactive`, because [CVC5](https://github.com/cvc5/cvc5) cannot answer `(get-model)` without the `--produce-models` option.)


### Debugging tips

* To troubleshoot your custom solver, you can use `print(smt(expr))` to print the SMT commands for your problem, call the solver from your own command-line and paste in the contents of your SMT file. Then issue the commands `(check-sat)` and, if satisfiable, `(get-model)`. This is exactly what Satisfiability.jl does when you call  `sat!`.
* Open your custom solver in interactive mode, try to solve the problem and then check its `command_history`. This is a list of all the commands sent to the solver. You can open an instance of the solver in your command line and paste in the commands to see the output for yourself. Look out for warnings and errors printed by the solver, which often cause output parsing errors.
* Startup messages and command prompts cause output parsing errors. Example: `cvc4 --lang smt2 --interactive --produce-models --incremental` prints both a startup message and a `CVC4>` command prompt that confuse our parser. Compare this to `cvc4 --interactive --produce-models --incremental --no-interactive-prompt` which doesn't include a command prompt or startup message. However, [CVC4](https://cvc4.github.io/) doesn't work for another reason discussed below.
* The solver should produce models or `sat!` won't work. The command `(get-model)` is issued internally when a problem is satisfiable.


### Open an issue!
We want `Satisfiability.jl` to be compatible with more solvers and are interested in investigating these issues. Please attach a minimum working example of your code and mention what OS you're on and how you installed the solver.

### Known issue: CVC4 doesn't work!
We are not aware of a way to make [CVC4](https://cvc4.github.io/) work with `Satisfiability.jl` because [CVC4](https://cvc4.github.io/) echoes the input to the output (see [issue #57](https://github.com/elsoroka/Satisfiability.jl/issues/57)). [CVC5](https://github.com/cvc5/cvc5) doesn't do this and works well. If you have a suggestion to get around this behavior, please let us know.

## Setting the solver logic
You can set the solver logic using an optional keyword argument in `sat!`.
The solver logic must be a string corresponding to a [valid SMT-LIB logic](http://smtlib.cs.uiowa.edu/logics.shtml). Users are responsible for selecting a logic that reflects the problem they intend to solve - `Satisfiability.jl` does not perform any correctness checking. Here's an example for [Yices](https://yices.csl.sri.com/), which **requires** the user to set the solver logic (some other solvers, such as [Z3](https://github.com/Z3Prover/z3) and [CVC5](https://github.com/cvc5/cvc5), will automatically infer a suitable logic if one isn't explicitly set).
```julia
status = sat!(expr, solver=Yices(), logic="QF_UFLIA")
```

### Custom interactions using `send_command`
`Satisfiability.jl` provides an interface to issue [SMT-LIB](https://smt-lib.org/language.shtml) commands and receive [SMT-LIB](https://smt-lib.org/language.shtml)-formatted solver responses programmatically. This is useful if you wish to build your own decision logic or parser using advanced solver functionality.

If you just want to use an [SMT solver](https://avigad.github.io/lamr/using_smt_solvers.html) interactively, for example by `push`ing or `pop`ping assertions, check out [Interactive Solving](interactive.md).

!!! note SMT-LIB solver modes.

In the [SMT-LIB](https://smt-lib.org/language.shtml) specification, after entering a problem and issuing the command `(check-sat)` the solver will be in either `sat` or `unsat` mode. The solver mode determines which commands are valid: for example, `(get-unsat-core)` is only valid in `unsat` mode and `(get-model)` is only valid in `sat` mode. You can find descriptions of modes and listings of valid commands in the latest [SMT-LIB Standard](http://www.smtlib.org/).

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

When using this functionality, you are responsible for keeping track of the solver mode and parsing the result of `send_command`. For convenience, `parse_model(model::String)` can parse the result of the [SMT-LIB](https://smt-lib.org/language.shtml) command `(get-model)`, returning a dictionary with variable names as keys and satisfying assignments as values.


**Checking if the response is complete**
Receiving a complete solver response is not as simple as it sounds, for two reasons.
1. The solver may take a long time to respond, for example when calling `(check-sat)`.
2. The solver's response may be large, thus it may be received in several chunks.

The `send_command` function has an optional argument `is_done` for checking whether the full response has been received. Two convenience functions are provided: `nested_parens_match(response::String)` returns `true` if `response` begins with `(` and ends with a matching `)`. This ensures the entire output is returned when issuing commands such as `(get-model)` where the entire response is wrapped in 1 set of parentheses. Many solver responses follow this format.
`is_sat_or_unsat` is very simple: if the response contains `sat` or `unsat` it returns `true`, otherwise it's `false`.

!!! warning Multiple parenthesized statements

If your command produces a response with multiple separate statements, for example `(statement_1)\n(statement_2)`, `nested_parens_match` is not guaranteed to return the entire response. The intended use case is `((statement_1)\n(statement_2))`. This should only happen if you issue two [SMT-LIB](https://smt-lib.org/language.shtml) commands at once.

**Customizing `is_done`**

A custom function `is_done(response::String)::Bool`, should have the following behavior:
* `is_done` returns `true` if the given `response` is valid (in whatever sense you define) and `false` if not.
* `send_command` will WAIT for more output while `is_done` is false.

[SAT solvers](https://avigad.github.io/lamr/using_sat_solvers.html) can be slow and some commands produce long outputs. Without `is_done`, `send_command` could receive a partial response and prematurely return.

For full implementation details, please see the [source code](https://github.com/elsoroka/Satisfiability.jl/blob/main/src/call_solver.jl) of `call_solver.jl`.
