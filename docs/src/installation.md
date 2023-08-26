# Installation
```@contents
Pages = ["installation.md"]
Depth = 3
```

**NOTE: To successfully use this package you will need to install a back-end solver.** [Z3](https://www.microsoft.com/en-us/research/publication/z3-an-efficient-smt-solver/) and [cvc5](https://cvc5.github.io/) are currently supported. You should be able to [use other solvers](advanced.md#Custom-solver-options-and-using-other-solvers) as long as they implement the SMT-LIB standard.

## Installing Satisfiability
You can install the latest version of Satisfiability with the command
`using Pkg; Pkg.add(url="https://github.com/elsoroka/Satisfiability.jl/")`
(TODO) Add official way when package is published.

## Installing a Solver
Satisfiability uses Julia's Base.Process library to interact with solvers. Thus to successfully install a solver for this package, all you need to do is make sure the appropriate command works in your machine's terminal.

### Debian Linux
**To install Z3**, use `sudo apt-get install z3`.
If you can launch Z3 from the command line by typing `z3 -smt2 -in`, your installation is correct.

**To install CVC5:**
* Download the appropriate binary [here](https://cvc5.github.io/downloads.html) and save it as `cvc5`. (Note: if you already have `cvc5` installed under the name `cvc5-linux`, make a symlink to the name `cvc5` or [customize your solver command](advanced.md#Custom-solver-options-and-using-other-solvers) to use the name `cvc5-linux`.)
* Set the executable permission: `chmod +x ./cvc5`.
* Most users should move the binary to `/usr/local/bin`. This allows it to be found from the command line.
If you can launch CVC5 from the command line by typing `cvc5 --interactive --produce-models`, your installation is correct.

### MacOS
**To install Z3**
* Download the appropriate zip file for the [latest Z3 release](https://github.com/Z3Prover/z3/releases) and install following the instructions on that page.
* If you can open your Terminal and launch z3 by typing `z3 -smt2 -in`, your installation is correct.

**To install CVC5**
* Download the appropriate binary [here](https://cvc5.github.io/downloads.html) and save it as `cvc5`. (Note: if you already have `cvc5` installed under another name, make a symlink to the name `cvc5` or [customize your solver command](advanced.md#Custom-solver-options-and-using-other-solvers) to use the name you already have.)
* Most users should move the binary to `/usr/local/bin`. This allows it to be found from the command line.
* If you can open your Terminal and launch CVC5 by typing `cvc5 --interactive --produce-models`, your installation is correct.

### Windows
**To install Z3**
* Download the appropriate zip file for the [latest Z3 release](https://github.com/Z3Prover/z3/releases).
* Unzip the file and put it in your applications folder.
* Find z3.exe. Typically this will be in a bin file in your unzipped folder. Don't move it, but make a note of this file path.
* Add the z3.exe file path to your PATH environment variable ([here's how to do this](https://helpdeskgeek.com/windows-10/add-windows-path-environment-variable/)).
If you can open the WIndows command line and launch z3 by typing `z3.exe -smt2 -in`, your installation is correct.

**To install cvc5**
* Download the [latest release](https://github.com/cvc5/cvc5/releases/) of cvc5. Make sure you save the exe file as `cvc5.exe`, not `cvc5-Win64.exe` or anything else.
* Make a note of the file path where you put cvc5.exe.
* Add the cvc5.exe file path to your PATH environment variable ([here's how to do this](https://helpdeskgeek.com/windows-10/add-windows-path-environment-variable/)).
If you can open the Windows command line and launch cvc5 by typing `cvc5 --interactive --produce-models`, your installation is correct.
