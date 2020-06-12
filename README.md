
[![Build Status](https://travis-ci.org/p4gauntlet/p4_tv.svg?branch=master)](https://travis-ci.org/p4gauntlet/p4_tv)

# The Gauntlet Tool Suite

Gauntlet is a set of tools design to find bugs in programmable data-plane compilers. More precisely, Gauntlet targets the
[P4 language](https://p4.org/) ecosystem and  the P4-16 reference compiler ([p4c](https://github.com/p4lang/p4c/)).

The goal is to ensure that a P4 compiler correctly translates a given input P4 program to its target-specific binary. The compiler must not crash and preserve the semantics of the program as originally written. The suite has three major components:

1. **Bludgeon**, a fuzz tester that generates random P4 programs using libraries repurposed from `p4c`.

2.  **Translation Validation**, which analyzes the intermediate representation of a program after each compiler pass and identifies potential discrepancies. We support translation validation for the open-source p4c compiler front- and mid-end libraries.

3. **Semantics-Guided Fuzzing**, which infers input and and corresponding output for a particular P4 program and generates end-to-end test packets. We have currently implemented semantics-guided fuzzing for the [bmv2 simple-switch](https://github.com/p4lang/behavioral-model) and the Tofino hardware switch.

##  Requirements
This repository works best with a recent version of Ubuntu (18.04+). The minimum required Python version is 3.6 (f-strings).

All tools require `p4c` to be installed. The fuzz tester and P4-to-Z3 converter are also p4c extensions which need to be copied into the `extensions` folder of the compiler. The `install.sh` contains detailed command instructions. Most dependencies can be installed by running `./install.sh` in the source folder (**Careful**, the installation assumes root privileges and installs several large packages).

To check whether everything has been installed correctly you can run `python3 -m pytest test.py -vrf`. This will take about 30 minutes.


## Instructions
### Generating a random program
After successful installation, you can generate a random P4 program via the `p4c/build/p4bludgeon out.p4 --arch top`  command. To generate Tofino code, the flag needs to be set to  `p4c/build/p4bludgeon --output out.p4 --arch tna`.
A typical crash checking workflow might be:

    p4c/build/p4bludgeon --output out.p4 --arch top && p4c/build/p4c-bm2-ss out.p4

### Retrieving Gauntlet semantics for a P4 program
For debugging purposes, you can run

    python3 get_semantics.py -i out.p4

to retrieve the semantic representation of a particular P4 program. This will print the z3 formula of each pipe in the package. These semantics can be used for equality comparison or test-case inference.

### Validating a P4C program
To validate that a program is compiled correctly by `p4c`, you can run

     p4c/build/p4bludgeon --output out.p4 --arch top && python3 check_p4_whitebox.py -i out.p4
`check_p4_compilation.py` checks if a sequence of P4 programs are all equivalent to each other using the `check_p4_pair.py` program as a sub routine. This sequence is produced by running p4c on an input P4 program. When p4c is run on an input P4 program, it produces a sequence of P4 programs, where each P4 program corresponds to the version of the input P4 program after a p4c optimization pass. This allows us to validate whether compilation/translation
is working correctly and to pinpoint the faulty optimization pass if it isn't
working correctly.

### Semantics-Guided Fuzzing

Semantics-guided fuzzing requires the behavioral model or the Tofino compiler to be installed. The correct binaries and include files need to be instrumented in the `check_p4_blackbox.py` file. Exact instructions will follow.
An example command is

     p4c/build/p4bludgeon --output out.p4 --arch v1model && python3 check_p4_blackbox.py -i out.p4 -r
This sequence of commands will first generate a random program, infer expected input and output values, convert them to a test file (in this case, they are stf files) and finally run a full test. If the observed output differs from the expected output, the tool will throw  an error. The `-r` flag denotes randomization of the input, it is optional.
To run semantics-guided fuzzing for the Tofino backend, `sudo` will have to be used.

     p4c/build/p4bludgeon --output out.p4 --arch tna && sudo -E python3 check_p4_blackbox.py -i out.p4 -r -t

### Fuzz-testing at Scale
We also include facilities to fuzz test the compilers at scale.

    python3 check_random_progs.py -i 1000
 To generate and compile a thousand programs using `p4c`.

    sudo -E python3 check_random_progs.py -i 1000 -t

 To generate and compile a thousand programs using the Tofino compiler.

     python3 check_random_progs.py -i 1000 -v

 To compile and validate a thousand programs using `p4c`.

     python3 check_random_progs.py -i 1000 -b -v

 To generate and fuzz test a thousand programs on the simple switch.

     python3 check_random_progs.py -i 1000 -t -v

 To generate and fuzz test a thousand programs on the Tofino compiler.
