# Installation
```@contents
Pages = ["installation.md"]
Depth = 3
```

**NOTE: To successfully use this package you need a back-end solver installed.** [Z3](https://www.microsoft.com/en-us/research/publication/z3-an-efficient-smt-solver/) will automatically be installed using `z3_jll`.

You can also use [cvc5](https://cvc5.github.io/) (although you will have to install it yourself). To use other solvers that implement the SMT-LIB standard, [check this page](advanced.md#Custom-solver-options-and-using-other-solvers) for guidelines.

## Installing Satisfiability
The usual way! `using Pkg; Pkg.add("Satisfiability")`
Satisfiability will automatically install Z3 on your system if it isn't already installed.

## Installing other Solvers
Satisfiability uses Julia's Base.Process library to interact with solvers. To successfully install a solver for this package, all you need to do is make sure the appropriate command works in your machine's terminal.

### Debian Linux

**To install CVC5:**
* Download the appropriate binary [here](https://cvc5.github.io/downloads.html) and save it as `cvc5`. (Note: if you already have `cvc5` installed under the name `cvc5-linux`, make a symlink to the name `cvc5` or [customize your solver command](advanced.md#Custom-solver-options-and-using-other-solvers) to use the name `cvc5-linux`.)
* Set the executable permission: `chmod +x ./cvc5`.
* Most users should move the binary to `/usr/local/bin`. This allows it to be found from the command line.
If you can launch CVC5 from the command line by typing `cvc5 --interactive --produce-models`, your installation is correct.

**To install Z3 manually** (you shouldn't need to do this), use `sudo apt-get install z3`.
If you can launch Z3 from the command line by typing `z3 -smt2 -in`, your installation is correct.

### MacOS

**To install CVC5**
* Download the appropriate binary [here](https://cvc5.github.io/downloads.html) and save it as `cvc5`. (Note: if you already have `cvc5` installed under another name, make a symlink to the name `cvc5` or [customize your solver command](advanced.md#Custom-solver-options-and-using-other-solvers) to use the name you already have.)
* Most users should move the binary to `/usr/local/bin`. This allows it to be found from the command line.
* If you can open your Terminal and launch CVC5 by typing `cvc5 --interactive --produce-models`, your installation is correct.


**To install Z3 manually** (you shouldn't need to do this):

* `brew install z3` should work if you have Homebrew installed.

Alternatively:

* Download the appropriate zip file for the [latest Z3 release](https://github.com/Z3Prover/z3/releases) and install following the instructions on that page.
* If you can open your Terminal and launch z3 by typing `z3 -smt2 -in`, your installation is correct.


### Windows

**To install cvc5**
* Download the [latest release](https://github.com/cvc5/cvc5/releases/) of cvc5. Make sure you save the exe file as `cvc5.exe`, not `cvc5-Win64.exe` or anything else.
* Make a note of the file path where you put cvc5.exe.
* Add the cvc5.exe file path to your PATH environment variable ([here's how to do this](https://helpdeskgeek.com/windows-10/add-windows-path-environment-variable/)).
If you can open the Windows command line and launch cvc5 by typing `cvc5 --interactive --produce-models`, your installation is correct.

**To install Z3 manually** (you shouldn't need to do this):
* Download the appropriate zip file for the [latest Z3 release](https://github.com/Z3Prover/z3/releases).
* Unzip the file and put it in your applications folder.
* Find z3.exe. Typically this will be in a bin file in your unzipped folder. Don't move it, but make a note of this file path.
* Add the z3.exe file path to your PATH environment variable ([here's how to do this](https://helpdeskgeek.com/windows-10/add-windows-path-environment-variable/)).
If you can open the WIndows command line and launch z3 by typing `z3.exe -smt2 -in`, your installation is correct.


### Installing Yices
Please follow the [official instructions](https://yices.csl.sri.com/).

## Installing other solvers
The workflow for installing any solver is the same!
* Download the solver
* Make sure you can invoke it from the command line. On Windows this might include adding its location to your system PATH variable.

The command you use is the command Satisfiability.jl will use. You can specify exactly the command you want by writing `solver = Solver("My Solver", `program_name --option1 --option2`)` - [see here](advanced.md) for more details.

Be aware of the limitations of your back-end solver - check the manual to ensure it supports the theories you plan to use, and make sure you set the right command line flags. If you're having difficulty using another solver, a good troubleshooting step is to `save` your problem to SMT format in Satisfiability.jl, then feed it to the solver on your command line.

**Satisfiability.jl does not warn you if your problem contains a theory or operation that your back-end solver does not support!** For example, if you set the wrong theory in Yices, `sat!` will hang.
Future versions of Satisfiability.jl may implement warnings about logic/problem mismatches, however difficulties can arise in maintaining the correctness of these warnings as solvers are updated and improved.