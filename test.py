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


# ***** P4-16 Standard Tests *****

# these tests show pathological behavior and can currently not be tested
slow_tests = [
    "header-stack-ops-bmv2.p4",
    "issue-2123-2-bmv2.p4",  # z3 gets stuck for unclear reasons
    "issue-2123-3-bmv2.p4",  # z3 gets stuck for unclear reasons
    "issue561-bmv2.p4",      # causes a segmentation fault
]
# create a list of all the programs in the p4c test folder
p416_tests = set()
for test in list(P4_DIR.glob("*.p4")):
    name = test.name
    if name in slow_tests:
        continue
    p416_tests.add(name)

# ***** tests that should trigger a violation bug *****

# these programs show pathological behavior and can currently not be tested
violation_filter = [
    "variable_shadowing",  # disabled until I have found a good solution
]
violation_tests = set()
for test in list(VIOLATION_DIR.glob("*")):
    name = test.name
    if name in violation_filter:
        continue
    violation_tests.add(name)

# ***** tests that should *NOT* trigger a violation bug *****

# these programs show pathological behavior and can currently not be tested
false_friends_filter = [
    "table_call_in_expression.p4",  # design flaw...
    "indirect_header_assign.p4",  # current bug
    "header_function_cast.p4",  # current bug
]
false_friends = set()
for test in list(FALSE_FRIENDS_DIR.glob("*")):
    name = test.name
    if name in false_friends_filter:
        continue
    false_friends.add(name)


# ***** broken tests, need fixing *****
xfails = [
    "array_field.p4",  # runtime index
    "array_field1.p4",  # runtime index
    "complex2.p4",  # runtime index
    "issue1989-bmv2.p4",  # runtime index
    "index.p4",  # runtime index
    "issue-2123.p4",  # runtime index
    "issue314.p4",  # runtime index
    "parser-conditional.p4",  # runtime index
    "runtime-index-2-bmv2.p4",  # runtime index
    "runtime-index-bmv2.p4",  # runtime index
    "side_effects.p4",  # runtime index
    "issue1334.p4",  # overloading, this test should normally not be skipped
    "logging.p4",  # string literal
    "string.p4",  # string literal
    "table-entries-range-bmv2.p4",  # range
    "fold_match.p4",  # range
    "pvs-struct-3-bmv2.p4",  # range
    "generic1.p4",  # complicated type inference
    "functors8.p4",  # complicated type inference
    "issue2303.p4",  # member precedence, fixed soon
    "issue1638.p4",  # member precedence, fixed soon
    "shadow-after-use.p4",  # another issue with shadowing
    # all of these do not work because of some quirk in inlining
    "issue1897-bmv2.p4",
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
