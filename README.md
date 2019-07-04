# p4_tv

This is a repository to test translation validation for the P4 Compiler.
It contains an analysis of the P4 compiler's optimization pass behavior and a z3 test framework to compare equivalence 
between P4 passes.

## Instructions
This repository requires an installed p4 compiler. You can install all dependencies by running `./install.sh` 
in the source folder.
You can run the pass anaylsis via `python3 pass_analysis.py`. It will create a pass folder containing a breakdown of each
P4 file and its corresponding passes. 

### Z3 P4
The `z3_py` folder contains examples of P4 programs expressed in z3py syntax. You can run the examples using `python3`.
