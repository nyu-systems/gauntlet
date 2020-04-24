import logging
from pathlib import Path

import pytest
import p4z3.util as util
import check_p4_whitebox as p4c_check
import check_p4_pair as z3_check

# configure logging
logging.basicConfig(filename="analysis.log",
                    format="%(levelname)s:%(message)s",
                    level=logging.INFO,
                    filemode="w")
stderr_log = logging.StreamHandler()
stderr_log.setFormatter(logging.Formatter("%(levelname)s:%(message)s"))
logging.getLogger().addHandler(stderr_log)

# some folder definitions
FILE_DIR = Path.resolve(Path(__file__)).parent
TARGET_DIR = FILE_DIR.joinpath("generated")
VIOLATION_DIR = FILE_DIR.joinpath("violated")
FALSE_FRIENDS_DIR = FILE_DIR.joinpath("false_friends")
P4_DIR = FILE_DIR.joinpath("p4c/testdata/p4_16_samples/")
# p4c binaries
P4C_BIN = FILE_DIR.joinpath("p4c/build/p4c")

# ***** working tests *****
p416_tests = []
# create a list of all the programs in the p4c test folder
all_tests = list(P4_DIR.glob("*.p4"))
for test in all_tests:
    p416_tests.append(test.name)

# ***** violation tests *****
violation_tests = [
    "basic_routing_stripped",
    "branching_in_function",
    "checksum2",
    "const_entries",
    "function_return",
    "copy_out",
    "drop-bmv2",
    "nested_slice",
    # "exit", exits are not allowed in functions so we do not have to worry... for now
    "action_exit",
    "equality-1",
    "equality-2",
    "equality_stripped",
    "issue1544-bmv2-1",
    "issue1544-bmv2-2",
    "key-bmv2",
    "key_inline",
    "issue983",
    "issue1642",
    "issue1781",
    "mux",
    "struct_initializer",
    "switch_statement",
    "unused_return",
    "out-params-1",
    "out-params-2",
    # "variable_shadowing", # disabled until I have found a good solution
]

# ***** tests that should not trigger a violation bug *****
false_friends = []
all_tests = list(FALSE_FRIENDS_DIR.glob("*.p4"))
for test in all_tests:
    false_friends.append(test.name)


# ***** broken tests, need fixing *****
xfails = [
    "array_field.p4",
    "array_field1.p4",
    "complex2.p4",
    "issue1989-bmv2.p4",
    "issue1334.p4",
    "logging.p4",
    "parser-conditional.p4",
    "runtime-index-2-bmv2.p4",
    "runtime-index-bmv2.p4",
    "side_effects.p4",
    "string.p4",
    "table-entries-range-bmv2.p4",
    "functors8.p4",
    # parser failures
    "fold_match.p4",
    "index.p4",  # runtimeindex
    "issue-2123.p4",  # runtimeindex
    "issue774-4-bmv2.p4",
    "issue774.p4",
    "pvs-struct-3-bmv2.p4",
    "issue314.p4",
    "issue1638.p4",
    # all of these do not work becauseof some quirk in inlining
    "inline-switch.p4",
    "issue1897-bmv2.p4",
    "issue1955.p4",
    "psa-example-digest-bmv2.p4",
    "issue2303.p4",
    "issue982.p4",  # something wrong with duplicate states, I do not get it...
    "issue1879-bmv2.p4",
    "shadow-after-use.p4", # another issue with shadowing
]

# these tests show pathological behavior and can currently not be tested
slow_tests = [
    "header-stack-ops-bmv2.p4",
    "issue-2123-2-bmv2.p4",  # z3 gets stuck for unclear reasons
    "issue-2123-3-bmv2.p4",  # z3 gets stuck for unclear reasons
    "issue561-bmv2.p4",      # causes a segmentation fault
    "table_call_in_expression.p4",  # design flaw...
]


def prep_test(p4_name, p4_dir=P4_DIR):
    p4_file = p4_dir.joinpath(p4_name)
    target_dir = TARGET_DIR.joinpath(p4_file.stem)
    util.del_dir(target_dir)
    util.check_dir(target_dir)
    return p4_file, target_dir


def run_z3p4_test(p4_file, target_dir):
    if p4_file.name in slow_tests:
        pytest.skip(f"Skipping slow test {p4_file}.")
        return util.EXIT_SKIPPED
    result = p4c_check.validate_translation(p4_file, target_dir, P4C_BIN)
    if result == util.EXIT_SKIPPED:
        pytest.skip(f"Skipping file {p4_file}.")
    return result


def run_violation_test(test_folder):
    test_folder = Path("violated").joinpath(test_folder)
    src_p4_file = test_folder.joinpath("orig.p4")
    src_py_file = test_folder.joinpath(f"{src_p4_file.stem}.py")
    p4c_check.run_p4_to_py(src_p4_file, src_py_file)
    for p4_file in list(test_folder.glob("**/[0-9]*.p4")):
        py_file = test_folder.joinpath(f"{p4_file.stem}.py")
        p4c_check.run_p4_to_py(p4_file, py_file)
        result = z3_check.z3_check([str(src_py_file), str(py_file)])
        if result != util.EXIT_VIOLATION:
            return util.EXIT_FAILURE
    return util.EXIT_SUCCESS


@pytest.mark.run_default
@pytest.mark.parametrize("test_name", p416_tests)
def test_bmv2(request, test_name):
    p4_file, target_dir = prep_test(test_name)
    request.node.custom_err = run_z3p4_test(p4_file, target_dir)
    if p4_file.name in xfails and request.node.custom_err != util.EXIT_SUCCESS:
        pytest.xfail(f"Expecting {p4_file} to fail.")
    assert request.node.custom_err == util.EXIT_SUCCESS


@pytest.mark.run_default
@pytest.mark.parametrize("test_name", false_friends)
def test_friends(request, test_name):
    p4_file, target_dir = prep_test(test_name, FALSE_FRIENDS_DIR)
    request.node.custom_err = run_z3p4_test(p4_file, target_dir)
    assert request.node.custom_err == util.EXIT_SUCCESS


@pytest.mark.run_default
@pytest.mark.parametrize("test_folder", violation_tests)
def test_violation(test_folder):
    assert run_violation_test(test_folder) == util.EXIT_SUCCESS


@pytest.mark.xfail
@pytest.mark.parametrize("test_name", xfails)
def test_xfails(request, test_name):
    p4_file, target_dir = prep_test(test_name)
    request.node.custom_err = run_z3p4_test(p4_file, target_dir)
    assert request.node.custom_err == util.EXIT_SUCCESS

# cat analysis.log |
# grep -Po '(?<=(Node )).*(?=not implemented)' | sort | uniq -c
