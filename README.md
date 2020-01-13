[![Build Status](https://travis-ci.org/p4gauntlet/p4_tv.svg?branch=master)](https://travis-ci.org/p4gauntlet/p4_tv)

# p4_tv

This is a repository for translation validation of the P4-16 Compiler (p4c).  The
goal is to check if the compiler translates a given input P4 program correctly
to a simplified "output" P4 program that is more amenable to running on
hardware. It has two components:

1. check_p4_pair.py checks if two P4 programs are semantically equivalent. It
does this by converting both P4 programs into Z3 formulas and asserting the equality
of the two formulas.

2. check_p4_compilation.py checks if a sequence of P4 programs are all
   equivalent to each other using the check_p4_pair.py program as a sub
routine. This sequence is produced by running p4c on an input P4 program. When
p4c is run on an input P4 program, it produces a sequence of P4 programs, where
each P4 program corresponds to the version of the input P4 program after a p4c
optimization pass. This allows us to validate whether compilation/translation
is working correctly and to pinpoint the faulty optimization pass if it isn't
working correctly.

## Instructions
This repository requires an installed P4 compiler. You can install all
dependencies by running `./install.sh` in the source folder.

To run a test on all p4 test provided by p4c you can run `python3 -m pytest test.py -vrf`.

To check that the compiler correctly translates a p4 program run `python3 check_p4_compilation.py -i "[P4_FILE]`. This program will create a pass folder called "validated" containing a breakdown of each P4 file and its corresponding passes. `check_p4_compilation.py` will emit an error if it detects a violating pass while compiling the program.

To compare two P4 programs, run `python3 check_p4_pair.py -progs [P4_FILE1],[P4_FILE2]`. If the programs are different an error is emitted.

