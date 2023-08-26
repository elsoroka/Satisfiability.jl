# FAQ
```@contents
Pages = ["faq.md"]
Depth = 3
```

## Where can I get help?
Please open a Github issue! This is a new package and we would love to hear your suggestions, bug reports, feature requests, and other commentary.

## Isn't this functionality included in JuMP?
[JuMP](https://jump.dev/) provides support for [integer and Boolean-valued variables](https://jump.dev/JuMP.jl/stable/manual/variables/#Binary-variables), however it is developed primarily to support mathematical optimization over real-valued or integer-valued variables and continuous functions. As such, JuMP interfaces with solvers such as ECOS, MOSEK, and Gurobi that are intended for continuous optimization problems. When you use JuMP to solve a problem with discrete variables, your solver will likely use a branch-and-bound style method.

### Should I use JuMP or Satisfiability.jl?
If you have a problem with mostly real variables and a few discrete integer or Boolean variables, you should probably use JuMP to call a branch-and-bound solver.

If you have a problem with only discrete variables, especially a large one, you should consider using an SMT solver. SMT can also represent specific variable types, like BitVectors, that JuMP cannot.

## How do I solve SMT problems in other langugages?
* In Python, you can use [PySMT](https://github.com/pysmt/pysmt) to access a wide variety of solvers.

* Similarly, Java has [JavaSMT](https://github.com/sosy-lab/java-smt).

* Solver-specific APIs include [CVC5 APIs](https://cvc5.github.io/docs/cvc5-1.0.2/api/api.html) for C++, Java, and Python.

* Z3 has [APIs](https://z3prover.github.io/api/html/index.html) for C, C++, .NET, Java, Python, and ML/OCaml. Additionally, Microsoft Research provides [tutorials](https://microsoft.github.io/z3guide/programming/Z3%20JavaScript%20Examples) for using Z3 in Python and JavaScript.

* Other solvers include PicoSAT, YICES, MathSAT and Boolector.

### Are there other SMT libraries in Julia?
* There are [Julia bindings](https://github.com/ahumenberger/Z3.jl) for the Z3 C++ API.
* PicoSAT also has [Julia bindings](https://github.com/sisl/PicoSAT.jl). You'll need to understand CNF format to use these.
* Here is a [package](https://github.com/dpsanders/SatisfiabilityInterface.jl) for modelling discrete constraint satisfaction problems and encoding them to Boolean satisfiability (SAT) problems. 

To our knowledge, Satisfiability.jl is the first general-purpose SMT library in Julia.

## What about other theories in the SMT standard?
In the future support may be added for additional theories supported in the SMTLIB2 standard, such as bitvectors and arrays.

## How can I retrieve a proof or unsat core from the solver?
Unsatisfiability proofs are difficult to support because the SMT2 standard doesn't specify their format - it's solver-dependent. Although we don't provide an explicit function, you can still retrieve a proof in two ways:

* Instead of calling `sat!`, use `save` to write the SMT representation of your problem to a file. Then invoke the solver from your command line, feed it the file and issue `(get-proof)` in `unsat` mode.
* Call `sat!` on your problem as shown [here](advanced.md#custom-interactions-with-solvers), then use `send_command` to issue `(get-proof)`.


## What does Satisfiability.jl actually do?
We provide a high-level interface to SMT solvers. SMT solvers can accept input in the [SMT2](http://www.smtlib.org/) format, which is very powerful but not easy to read. When you specify an SMT problem in Satisfiability.jl and call `sat!`, we generate an SMT2-formatted **representation** of the problem, feed it to a solver, then interpret the result.

# LFAQ
(Less frequently-asked questions.)

## Why is `sat!` so slow for real-valued variables?
Because the SMT theory of real-valued variables is incomplete.

