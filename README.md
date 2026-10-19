
[![Build Status](https://github.com/nyu-systems/gauntlet/actions/workflows/pytest.yaml/badge.svg)](https://github.com/nyu-systems/gauntlet/actions/workflows/pytest.yaml)

# The Gauntlet Tool Suite

- [Introduction](#introduction)
- [Requirements](#requirements)
  * [Frameworks for Model-Based Testing](#frameworks-for-model-based-testing)
- [Instructions](#instructions)
  * [Generating a Random Program](#generating-a-random-program)
  * [Retrieving Gauntlet Semantics for a P4 Program](#retrieving-gauntlet-semantics-for-a-p4-program)
  * [Validating a P4C Program](#validating-a-p4c-program)
  * [Model-Based Testing](#model-based-testing)
  * [Fuzz-Testing at Scale](#fuzz-testing-at-scale)
- [Fuzz-Testing Support Matrix](#fuzz-testing-support-matrix)
- [Bugs Found in P4 Compilers](#bugs-found-in-p4-compilers)
- [Citing This Project](#citing-this-project)

## Introduction
Gauntlet is a set of tools designed to find bugs in programmable data-plane compilers. More precisely, Gauntlet targets the
[P4 language](https://p4.org/) ecosystem and  the P4-16 reference compiler ([p4c](https://github.com/p4lang/p4c/)).

The goal is to ensure that a P4 compiler correctly translates a given input P4 program to its target-specific binary. The compiler must not crash and preserve the semantics of the program as originally written. The suite has three major components:

1. **P4Smith** (formerly Bludgeon), a random P4 program generator now merged into [P4C](https://p4lang.github.io/p4c/p4smith.html).

2.  **Translation Validation**, which analyzes the intermediate representation of a program after each compiler pass and identifies potential discrepancies. We support translation validation for the open-source p4c compiler front- and mid-end libraries.

3. **Model-based Testing**, which infers input and and corresponding output for a particular P4 program and generates end-to-end test packets. We have currently implemented model-based testing for the [bmv2 simple-switch](https://github.com/p4lang/behavioral-model) and the Tofino hardware switch.

For more details and a broad overview of the concepts in Gauntlet, refer to our [OSDI paper](https://www.usenix.org/conference/osdi20/presentation/ruffy).

##  Requirements
This repository runs best with a recent version of Ubuntu (22.04). Current P4C builds require a C++20 toolchain and Python 3.10 or newer.

All tools require `p4c` to be installed. The P4-to-Z3 converter is a p4c extension which needs to be copied or symlinked into the `extensions` folder of the compiler. See the [ToZ3 build instructions](modules/toz3/README.md). P4Smith is built through P4C's P4Tools framework, with `-DENABLE_TEST_TOOLS=ON -DENABLE_TOOLS_MODULE_SMITH=ON`. The `do_install.sh` contains dependency installation instructions (**Careful**, the installation assumes root privileges and installs several large packages), but currently disables P4Tools and therefore does not build P4Smith.

To check the installation, run `ctest --test-dir modules/p4c/build --output-on-failure -j 2 -R '^(toz3-|pruner)'`. See [ToZ3's testing instructions](modules/toz3/README.md#usage) for the build targets, memory limit, and expected failures.

###  Frameworks for Model-based Testing
Model-based testing requires a full test harness. Gauntlet currently supports the [bmv2 simple-switch](https://github.com/p4lang/behavioral-model) and the Tofino packet test framework. The behavioral model can be installed running the installation script with the option `./do_install.sh INSTALL_BMV2=ON`.

The Tofino test framework requires access to the SDK and a manual setup. Gauntlet's scripts assume that the folder is installed under `tofino/bf_src`. We typically run the installation script as `./tofino/bf_src/p4studio_build/p4studio_build.py --use-profile p416_examples_profile`.


## Instructions
### Generating a Random Program
After successful installation, you can generate a random P4 program with `modules/p4c/build/p4smith --target generic --arch core out.p4`. To generate Tofino code, use `modules/p4c/build/p4smith --target tofino --arch tna out.p4`. The output filename is positional; use `--seed` to reproduce a program with the same generator revision.
A typical crash checking workflow might be:

    modules/p4c/build/p4smith --target generic --arch core out.p4 && modules/p4c/build/p4test out.p4

### Retrieving Gauntlet Semantics for a P4 Program
For debugging purposes, you can run

    bin/get_p4_semantics out.p4

to retrieve the semantic representation of a particular P4 program. This will print the Z3 formula of each pipe in the package. Parser outputs are included, with models for core packet operations. These semantics can be used for equality comparison; see [ToZ3's documentation](modules/toz3/README.md) for current limitations.

### Validating a P4C Program
To validate that a program is compiled correctly by `p4c`, you can run

     modules/p4c/build/p4smith --target generic --arch core out.p4 && bin/validate_p4_translation --compiler-bin modules/p4c/build/p4test --allow-undefined out.p4
`bin/validate_p4_translation` invokes the native `p4validate` tool to compare successive compiler snapshots. `--allow-undefined` tolerates differences attributed to undefined behavior; omit it for strict comparison. This sequence is produced by running p4c on an input P4 program. When p4c is run on an input P4 program, it produces a sequence of P4 programs, where each P4 program corresponds to the version of the input P4 program after a p4c optimization pass. This allows us to validate whether compilation/translation is working correctly and to pinpoint the faulty optimization pass if it isn't
working correctly.

### Model-Based Testing [DEPRECATED]

This deprecated workflow still requires Bludgeon and Python IR output from `p4toz3`; it requires interface updates to work with P4Smith and native ToZ3. Model-based testing requires the behavioral model or the Tofino compiler to be installed. The correct binaries and include files need to be instrumented in the `src/generate_p4_test.py` file. An example command is

     modules/p4c/build/p4bludgeon --output out.p4 --arch v1model && bin/generate_test_case -i out.p4 -r
This sequence of commands will first generate a random program, infer expected input and output values, convert them to a test file (in this case, they are stf files) and finally run a full test. If the observed output differs from the expected output, the tool will throw  an error. The `-r` flag denotes randomization of the input, it is optional.
To run model-based testing for the Tofino back end, `sudo` will have to be used.

     modules/p4c/build/p4bludgeon --output out.p4 --arch tna && sudo -E bin/generate_test_case -i out.p4 -r --arch tna

### Fuzz-Testing at Scale
We also include facilities to fuzz test the compilers at scale. The examples below use legacy scripts that still expect `p4bludgeon` and Python IR output; they require migration to P4Smith and native ToZ3.

    bin/test_random_progs -i 1000
 To generate and compile a thousand programs using P4C's `p4test`.

    sudo -E bin/test_random_progs -i 1000 --arch tna

 To generate and compile a thousand programs using the Tofino compiler.

     bin/test_random_progs -i 1000 -v

 To compile and validate a thousand programs using P4C's `p4test`.

     bin/test_random_progs -i 1000 --arch v1model -b

 To generate and fuzz test a thousand programs on the simple switch.

     sudo -E bin/test_random_progs -i 1000 --arch tna -b

 To generate and fuzz test a thousand programs on the Tofino compiler.

## Fuzz-Testing Support Matrix

Model-based testing entries refer to the deprecated workflow above; current translation-validation coverage and limitations are documented in [ToZ3](modules/toz3/README.md).

| Architecture | Compiler | P4Smith Support | Validation Testing | Model-based Testing (deprecated) |
| ------------- | ------------- | ------------- | ------------- | ------------- |
| psa | `p4c-bm2-psa` | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: |
| tna | `p4c-bf` | :heavy_check_mark: | :x: | :heavy_check_mark: |
| core | `p4test` | :heavy_check_mark: | :heavy_check_mark: | :x: |
| v1model | `p4c-bm2-ss` | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: |

## Bugs Found in P4 Compilers

We also track the bugs we have found. A detailed breakdown can be found in the [bugs](bugs) folder.

## Citing This Project

To cite our work please refer to our paper:

```tex
@inproceedings {gauntlet,
  title = {Gauntlet: Finding Bugs in Compilers for Programmable Packet Processing},
  booktitle = {14th {USENIX} Symposium on Operating Systems Design and Implementation ({OSDI} 20)},
  year = {2020},
  url = {https://www.usenix.org/conference/osdi20/presentation/ruffy},
  publisher = {{USENIX} Association},
  month = nov,
}
```
