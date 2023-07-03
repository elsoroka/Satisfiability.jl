# Installation
**NOTE: To successfully use this package you will need to install a back-end solver.** Currently, we support [Z3](https://www.microsoft.com/en-us/research/publication/z3-an-efficient-smt-solver/) and [CVC5](https://cvc5.github.io/). You may [use other solvers](advanced.md#Custom-solver-options-and-using-other-solvers) at your own risk.

## Installing BooleanSatisfiability
You can install the latest version of BooleanSatisfiability with the command
`using Pkg; Pkg.add(url="https://github.com/elsoroka/BooleanSatisfiability.jl/")`
(TODO) Add official way when package is published.

## Installing a Solver
BooleanSatisfiability uses Julia's Base.Process library to interact with solvers. Thus to successfully install a solver for this package, all you need to do is make sure the appropriate command (listed below) works in your machine's terminal.

### Debian Linux
**To install Z3:**
* The easiest way is to type `sudo apt-get install z3`
If you can launch Z3 from the command line by typing `z3 -smt2 -in`, your installation is correct.

**To install cvc5:**
* Download the appropriate binary [here](https://cvc5.github.io/downloads.html) and save it as `cvc5`. (Note: if you already have `cvc5` installed under the name `cvc5-linux`, make a symlink to the name `cvc5` or [customize your solver command](advanced.md#Custom-solver-options-and-using-other-solvers).
* Set the executable permission: `chmod +x ./cvc5`
* Most users will want to move the binary to `/usr/local/bin` so you can easily invoke it from the command line.
If you can launch cvc5 from the command line by typing `cvc5 --interactive --produce-models`, your installation is correct.

### OS X
(TODO)

### Windows
(TODO)