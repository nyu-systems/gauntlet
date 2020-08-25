
[![Build Status](https://travis-ci.com/p4gauntlet/p4_tv.svg?branch=master)](https://travis-ci.com/p4gauntlet/p4_tv)

# The Gauntlet Tool Suite

Gauntlet is a set of tools design to find bugs in programmable data-plane compilers. More precisely, Gauntlet targets the
[P4 language](https://p4.org/) ecosystem and  the P4-16 reference compiler ([p4c](https://github.com/p4lang/p4c/)).

The goal is to ensure that a P4 compiler correctly translates a given input P4 program to its target-specific binary. The compiler must not crash and preserve the semantics of the program as originally written. The suite has three major components:

1. **Bludgeon**, a fuzz tester that generates random P4 programs using libraries repurposed from `p4c`.

2.  **Translation Validation**, which analyzes the intermediate representation of a program after each compiler pass and identifies potential discrepancies. We support translation validation for the open-source p4c compiler front- and mid-end libraries.

3. **Model-based Testing**, which infers input and and corresponding output for a particular P4 program and generates end-to-end test packets. We have currently implemented model-based testing for the [bmv2 simple-switch](https://github.com/p4lang/behavioral-model) and the Tofino hardware switch.

For more details and a broad overview of the concepts in Gauntlet, refer to our [preprint](https://arxiv.org/abs/2006.01074).

##  Requirements
This repository run best with a recent version of Ubuntu (18.04+). The minimum required Python version is 3.6 ([f-strings](https://www.python.org/dev/peps/pep-0498/)).

All tools require `p4c` to be installed. The fuzz tester and P4-to-Z3 converter are also p4c extensions which need to be copied or symlinked into the `extensions` folder of the compiler. The `do_install.sh` contains detailed command instructions. Most dependencies can be installed by running `./do_install.sh` in the source folder (**Careful**, the installation assumes root privileges and installs several large packages).

To check whether everything has been installed correctly you can run `python3 -m pytest test.py -vrf`. This will take about 30 minutes.

###  Frameworks for model-based testing
Model-based testing requires a full test harness. Gauntlet currently supports the [bmv2 simple-switch](https://github.com/p4lang/behavioral-model) and the Tofino packet test framework. The behavioral model can be installed running the installation script with the option `./do_install.sh INSTALL_BMV2=ON`.

The Tofino test framework requires access to the SDK and a manual setup. Gauntlet's scripts assume that the folder is installed under `tofino/bf_src`. We typically run the installation script as `./tofino/bf_src/p4studio_build/p4studio_build.py --use-profile p416_examples_profile`.


## Instructions
### Generating a random program
After successful installation, you can generate a random P4 program via the `modules/p4c/build/p4bludgeon out.p4 --arch top`  command. To generate Tofino code, the flag needs to be set to  `modules/p4c/build/p4bludgeon --output out.p4 --arch tna`.
A typical crash checking workflow might be:

    modules/p4c/build/p4bludgeon --output out.p4 --arch top && modules/p4c/build/p4c-bm2-ss out.p4

### Retrieving Gauntlet semantics for a P4 program
For debugging purposes, you can run

    python3 get_semantics.py -i out.p4

to retrieve the semantic representation of a particular P4 program. This will print the Z3 formula of each pipe in the package. These semantics can be used for equality comparison or test-case inference.

### Validating a P4C program
To validate that a program is compiled correctly by `p4c`, you can run

     modules/p4c/build/p4bludgeon --output out.p4 --arch top && python3 validate_p4_translation.py -i out.p4
`check_p4_compilation.py` checks if a sequence of P4 programs are all equivalent to each other using the `check_p4_pair.py` program as a sub routine. This sequence is produced by running p4c on an input P4 program. When p4c is run on an input P4 program, it produces a sequence of P4 programs, where each P4 program corresponds to the version of the input P4 program after a p4c optimization pass. This allows us to validate whether compilation/translation is working correctly and to pinpoint the faulty optimization pass if it isn't
working correctly.

### Model-based Testing

Model-based testing requires the behavioral model or the Tofino compiler to be installed. The correct binaries and include files need to be instrumented in the `generate_p4_test.py` file. An example command is

     modules/p4c/build/p4bludgeon --output out.p4 --arch v1model && python3 generate_p4_test.py -i out.p4 -r
This sequence of commands will first generate a random program, infer expected input and output values, convert them to a test file (in this case, they are stf files) and finally run a full test. If the observed output differs from the expected output, the tool will throw  an error. The `-r` flag denotes randomization of the input, it is optional.
To run model-based testing for the Tofino backend, `sudo` will have to be used.

     modules/p4c/build/p4bludgeon --output out.p4 --arch tna && sudo -E python3 generate_p4_test.py -i out.p4 -r -t

### Fuzz-testing at Scale
We also include facilities to fuzz test the compilers at scale.

    python3 check_random_progs.py -i 1000
 To generate and compile a thousand programs using P4C's `p4test`.

    sudo -E python3 check_random_progs.py -i 1000 --arch tna

 To generate and compile a thousand programs using the Tofino compiler.

     python3 check_random_progs.py -i 1000 -v

 To compile and validate a thousand programs using P4C's `p4test`.

     python3 check_random_progs.py -i 1000 --arch v1model -b

 To generate and fuzz test a thousand programs on the simple switch.

     python3 check_random_progs.py -i 1000 --arch tna -b

 To generate and fuzz test a thousand programs on the Tofino compiler.

#### Fuzz-testing Support Matrix

| Architecture | Compiler | Bludgeon Support | Validation Testing | Model-based Testing |
| ------------- | ------------- | ------------- | ------------- | ------------- |
| psa | `p4c-bm2-psa` | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: |
| tna | `p4c-bf` | :heavy_check_mark: | :x: | :heavy_check_mark: |
| top | `p4test` | :heavy_check_mark: | :heavy_check_mark: | :x: |
| v1model | `p4c-bm2-ss` | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: |
