import logging
from pathlib import Path

import pytest
import p4z3.util as util
import check_p4_compilation as p4c_check
import check_p4_pair as z3_check

# configure logging
logging.basicConfig(filename="analysis.log",
                    format="%(levelname)s:%(message)s",
                    level=logging.INFO,
                    filemode='w')
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
P4C_BIN_1863 = FILE_DIR.joinpath("p4c_bins/issue1863")

# ***** working tests *****
p416_tests = []
# create a list of all the programs in the p4c test folder
all_tests = list(P4_DIR.glob("*.p4"))
for test in all_tests:
    p416_tests.append(test.name)

# ***** violation tests *****
violation_tests = [
    "basic_routing_stripped",
    "checksum2",
    "const_entries",
    "copy_out",
    "drop-bmv2",
    "equality-1",
    "equality-2",
    "equality_stripped",
    "issue1544-bmv2-1",
    "issue1544-bmv2-2",
    "key-bmv2",
    "issue1642",
    "issue1781",
    "mux",
    "out-params-1",
    "out-params-2",
]

# ***** tests that should not trigger a violation bug *****
false_friends = []
all_tests = list(FALSE_FRIENDS_DIR.glob("*.p4"))
for test in all_tests:
    false_friends.append(test.name)


# ***** broken tests, need fixing *****
xfails = [
    "checksum1-bmv2.p4",
    "checksum2-bmv2.p4",
    "checksum3-bmv2.p4",
    "fabric.p4",
    "header-stack-ops-bmv2.p4",
    "hit-expr-bmv2.p4",
    "issue1566-bmv2.p4",
    "issue1566.p4",
    "issue1653-complex-bmv2.p4",
    "issue1765-bmv2.p4",
    "issue1814-1-bmv2.p4",
    "issue1814-bmv2.p4",
    "issue1937-1-bmv2.p4",
    "issue1989-bmv2.p4",
    "issue486-bmv2.p4",
    "issue496.p4",
    "issue949.p4",
    "issue561-2-bmv2.p4",
    "issue561-7-bmv2.p4",
    "junk-prop-bmv2.p4",
    "table-entries-range-bmv2.p4",
    "table-entries-ser-enum-bmv2.p4",
    "v1model-p4runtime-most-types1.p4",
    "v1model-special-ops-bmv2.p4",
    "array_field.p4",
    "array_field1.p4",
    "cases.p4",
    "cast_noop.p4",
    "complex.p4",
    "complex1.p4",
    "complex10.p4",
    "complex2.p4",
    "concat.p4",
    "control-as-param.p4",
    "default-package-argument.p4",
    "default-switch.p4",
    "direct-action.p4",
    "direct-action1.p4",
    "emptyTuple.p4",
    "enum-bmv2.p4",
    "bool_cast.p4",
    "constant_folding.p4",
    "functors9.p4",
    "issue1544-2.p4",
    "exit4.p4",
    "function.p4",
    "functors6.p4",
    "functors7.p4",
    "functors8.p4",
    "generic1.p4",
    "hit_ebpf.p4",
    "inline-control.p4",
    "inline-control1.p4",
    "inline-switch.p4",
    "issue1208-1.p4",
    "issue1304.p4",
    "issue1334.p4",
    "issue1386.p4",
    "issue1540.p4",
    "issue1638.p4",
    "issue1717.p4",
    "issue1806.p4",
    "issue1830.p4",
    "issue2036-3.p4",
    "issue2044-bmv2.p4",
    "issue313_1.p4",
    "issue313_2.p4",
    "issue344.p4",
    "issue396.p4",
    "issue407-2.p4",
    "issue407-3.p4",
    "issue754.p4",
    "issue803-2.p4",
    "issue803-3.p4",
    "issue933.p4",
    "issue982.p4",
    "key-issue-1020_ebpf.p4",
    "large.p4",
    "list-compare.p4",
    "lj_example.p4",
    "named-arg1.p4",
    "nested-tuple.p4",
    "p4rt_digest_complex.p4",
    "package.p4",
    "parser-conditional.p4",
    "psa-action-profile1.p4",
    "psa-action-profile2.p4",
    "psa-action-profile3.p4",
    "psa-action-profile4.p4",
    "psa-action-selector1.p4",
    "psa-action-selector3.p4",
    "psa-basic-counter-bmv2.p4",
    "psa-counter1.p4",
    "psa-counter2.p4",
    "psa-counter3.p4",
    "psa-counter4.p4",
    "psa-counter6.p4",
    "psa-drop-all-bmv2.p4",
    "psa-drop-all-corrected-bmv2.p4",
    "psa-example-counters-bmv2.p4",
    "psa-example-digest-bmv2.p4",
    "psa-example-parser-checksum.p4",
    "psa-fwd-bmv2.p4",
    "psa-hash.p4",
    "psa-meter1.p4",
    "psa-meter3.p4",
    "psa-meter4.p4",
    "psa-meter5.p4",
    "psa-meter6.p4",
    "psa-multicast-basic-bmv2.p4",
    "psa-multicast-basic-corrected-bmv2.p4",
    "psa-portid-using-newtype2.p4",
    "psa-random.p4",
    "psa-recirculate-no-meta-bmv2.p4",
    "psa-register1.p4",
    "psa-register2.p4",
    "psa-register3.p4",
    "psa-resubmit-bmv2.p4",
    "psa-test.p4",
    "psa-top-level-assignments-bmv2.p4",
    "psa-unicast-or-drop-bmv2.p4",
    "psa-unicast-or-drop-corrected-bmv2.p4",
    "register-serenum.p4",
    "serenum.p4",
    "side_effects.p4",
    "simplify.p4",
    "spec-ex12.p4",
    "stack.p4",
    "stack2.p4",
    "string.p4",
    "struct_init-1.p4",
    "logging.p4",
    "nested-tuple1.p4",
    "pipe.p4",
    "psa-action-selector2.p4",
    "psa-example-register2-bmv2.p4",
    "table-key-serenum.p4",
    "tuple.p4",
    "tuple0.p4",
    "tuple1.p4",
    "tuple2.p4",
    "two_ebpf.p4",
    "unreachable-accept.p4",
    "v1model-digest-containing-ser-enum.p4",
    "vss-example.p4",
]

slow_tests = [
    "flowlet_switching-bmv2.p4",
    # "issue-2123.p4",
    "issue-2123-2-bmv2.p4",
    "issue-2123-3-bmv2.p4",
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
    if p4_file.name in xfails:
        pytest.xfail(f"Expecting {p4_file} to fail.")
    request.node.custom_err = run_z3p4_test(p4_file, target_dir)
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


@pytest.mark.run_default
@pytest.mark.skip(reason="binary currently broken")
def test_issue1863_broken():
    # ***** actual custom violation *****
    p4_dir = Path("violated/issue1863/")
    p4_file, target_dir = prep_test("issue1863-bmv2.p4", p4_dir)
    result = p4c_check.validate_translation(p4_file, target_dir, P4C_BIN_1863)
    assert result == util.EXIT_VIOLATION

# cat analysis.log |
# grep -Po '(?<=(Node )).*(?=not implemented)' | sort | uniq -c
