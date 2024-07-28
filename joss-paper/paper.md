---
title: 'Satisfiability.jl: Satisfiability Modulo Theories in Julia'
tags:
  - Julia
  - formal verification
  - satisfiability modulo theories
authors:
  - name: Emiko Soroka
    orcid: 0009-0001-2710-469X
    affiliation: 1
    corresponding: true
  - name: Mykel J. Kochenderfer
    orcid: 0000-0002-7238-9663
    affiliation: 1
    corresponding: true
  - name: Sanjay Lall
    orcid: 0000-0002-1783-5309
    affiliation: 2
    corresponding: true
affiliations:
 - name: Stanford University Department of Aeronautics and Astronautics, Stanford CA 94305, USA
   index: 1
 - name: Stanford University Department of Electrical Engineering, Stanford CA 94305, USA
   index: 2
date: 1 March 2024
bibliography: bibliography.bib
---

# Summary
Theorem proving software is one of the core tools in formal verification, model checking, and synthesis. Modern provers solve satisfiability modulo theories (SMT) problems encompassing propositional logic, integer and real arithmetic, floating-point arithmetic, strings, and data structures such as bit vectors [@de2011satisfiabilityintro]. Additionally, new theories and heuristics are continually being developed, increasing the practical utility of SMT [@bjorner2023satisfiability; @saouli2023cosysel]. 

This paper introduces `Satisfiability.jl`, a package providing a high-level representation for SMT formulae including propositional logic, integer and real-valued arithmetic, and bit vectors in Julia [@bezanson2017julia]. `Satisfiability.jl` is the first published package for SMT solving in idiomatic Julia, taking advantage of language features such as multiple dispatch and metaprogramming to simplify the process of specifying and solving an SMT problem.

## The SMT-LIB specification language
SMT-LIB is a low-level specification language designed to standardize interactions with theorem provers[^1].
(To disambiguate between the SMT (satisfiability modulo theories) and this specification language, we always refer to the language as SMT-LIB.) There are both in-depth treatments of computational logic and associated decision procedures [@bradley2007calculus; @kroening2016decision] and shorter overviews of SMT [@de2011satisfiabilityintro].

SMT-LIB uses a Lisp-like syntax designed to simplify input parsing, providing an interactive interface for theorem proving similar to Julia's REPL. The language supports declaring variables, defining functions, making assertions (requiring that a Boolean predicate be true), and issuing solver commands. However, a limitation of SMT-LIB is that many commands are only valid in specific solver modes. The command `(get-model)`, for example, retrieves the satisfying assignment for a predicate and is only valid in `sat` mode, while `(get-unsat-core)` is only valid in `unsat` mode. Issuing a command in the wrong mode yields an error, thus many useful sequences of SMT-LIB commands cannot be scripted in advance.

For a full description of SMT-LIB, readers are referred to the standard [@smtlib2]. Because our software provides an abstraction on top of SMT-LIB (thus offering compatibility with different SMT solver backends), we refrain from an in-depth description of the language. Knowledge of SMT-LIB is not required to use `Satisfiability.jl`.

# Statement of need
Many theorem provers have been developed over the years. Some notable provers include Z3 [@z3], PicoSAT [@biere2008picosat], and CVC5 [@cvc5], all of which expose APIs in popular languages including C++ and Python. However, provers are low-level tools intended to be integrated into other software, necessitating the development of higher-level software to improve usability. Such packages been published for other common languages: `PySMT` uses both solver-specific APIs and the SMT-LIB language to interact with a variety of solvers [@pysmt2015]. `JavaSMT` and `ScalaSMT` are similar [@baier2021javasmt; @cassez2017scalasmt]. In C++, the SMT-Switch library exposes many of the underlying SMT-LIB commands [@mann2021smt].

By comparison, SMT solving in Julia has historically required the use of wrapped C++ APIs to access specific solvers. Z3 and PicoSAT, among others, provide Julia APIs through this method, allowing access to some or all functionality at a lower level of abstraction [@picosat_jl]. However, wrapped APIs often provide interfaces that do not match the idioms or best practices of a specific language. Thus a native Julia front-end for SMT solving has the potential to greatly improve the accessibility of formal verification in Julia.
`Satisfiability.jl` is the first such tool to be published in the Julia ecosystem. It facilitates the construction of SMT formulae and the automatic generation of SMT-LIB statements, as well as programmatic interaction with SMT-LIB compliant theorem provers.

# Functionality
Satisfiability.jl uses multiple dispatch to optimize and simplify operations over constants, the type system to enforce the correctness of SMT expressions, and Julia's system libraries to interact with SMT-LIB compliant solvers.

* Variables are defined using macros, similarly to JuMP.jl [@Lubin2023]. Expressions are constructed from variables and SMT-LIB operators. Where applicable, we define the appropriate mathematical operator symbols using Julia's operator precedence rules and Unicode support. We also use the built-in array functionality to broadcast operators across arrays of expressions, a feature that is not available in the underlying SMT-LIB language.

* Constants are automatically wrapped. Julia's native \verb|Bool|, \verb|Int|, and \verb|Float64| types interoperate with our \verb|BoolExpr|, \verb|IntExpr| and \verb|RealExpr| types following type promotion rules. Numeric constants are simplified and promoted; for example, \verb|true + 2| is stored as integer \verb|3| and \verb|1 + 2.5| is promoted to \verb|3.5|. Logical expressions involving constants are simplified using multiple dispatch to handle special cases.

* We use Julia's type system to prevent expressions with incompatible types from being constructed and to automatically convert compatible types following Z3's promotion rules. For example, adding a Boolean `z` and integer `a` yields the expression  `ite(z, 1, 0) + a` (where `ite` is the if-then-else operator).

* An uninterpreted function is a function where the input-output mapping is not known. When uninterpreted functions appear in SMT formulae, the task of the solver is to construct a representation of the function using operators in the appropriate theories, or to determine that no function exists (the formula is unsatisfiable). `Satisfiability.jl` implements uninterpreted functions using Julia's metaprogramming capabilities to generate correctly typed functions returning either SMT expressions or (if a satisfying assignment is known), the correct value when evaluating a constant.


## Interacting with solvers
Internally, our package launches a solver as an external process and interacts with it via input and output pipes. This supports the interactive nature of SMT-LIB, which necessitates a two-way connection with the solver, and provides several benefits. By transparently documenting how our software manages sessions with solvers, we eliminate many of the difficulties that arise when calling software dependencies. We also unify the process of installing solvers for `Satisfiability.jl` across operating systems; the user simply ensures the solver can be invoked from their machine's command line. Users may customize the command used to invoke a solver, providing a single mechanism for interacting with any SMT-LIB compatible solver; customizing options using command line flags; and working around machine-specific issues such as a solver being available under a different name or at a specific path.


## Interactive solving
SMT-LIB was designed as an interactive interface, allowing users to modify the assertions of an SMT problem and issue follow-up commands after a `sat` or `unsat` response. `Satisfiability.jl` provides an interactive mode for these use cases, in which users can manage the solver assertion stack using `push!`, `pop!`, and `assert!` commands.


# Future work
Two planned improvements to `Satisfiability.jl` include adding support for the remaining SMT-LIB standard theories and adding the ability to automatically determine the \textit{logic type} of an assertion, a property describing what types of variables and expressions are present, which is used by solvers to determine the best algorithm for a particular problem.


# Acknowledgments
The software architecture of `Satisfiability.jl` was inspired by `Convex.jl` and `JuMP.jl` [@convexjl; @Lubin2023]. Professor Clark Barrett provided valuable advice on understanding the SMT-LIB standard and on interface design for SMT solving.

This research was supported by Ford Motor Co. under the Stanford-Ford Alliance, agreement number 235158.

# References

[^1]: The current SMT-LIB standard is V2.6; we used this version of the language specification when implementing our software.