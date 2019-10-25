import logging
from pathlib import Path

import pytest
import p4z3.util as util
import check_p4_compilation as p4c_check
import check_p4_pair as z3_check

# configure logging
logging.basicConfig(filename="test.log",
                    format="%(levelname)s:%(message)s",
                    level=logging.INFO)
log = logging.getLogger(__name__)

# some folder definitions
FILE_DIR = Path.resolve(Path(__file__)).parent
TARGET_DIR = FILE_DIR.joinpath("generated")
VIOLATION_DIR = FILE_DIR.joinpath("violated")
P4_DIR = FILE_DIR.joinpath("p4c/testdata/p4_16_samples/")

# p4c binaries
P4C_BIN = FILE_DIR.joinpath("p4c/build/p4c-bm2-ss")
P4C_BIN_1863 = FILE_DIR.joinpath("p4c_bins/issue1863")


def prep_test(p4_name, p4_dir=P4_DIR):
    p4_file = p4_dir.joinpath(p4_name)
    target_dir = TARGET_DIR.joinpath(p4_file.stem)
    util.del_dir(target_dir)
    util.check_dir(target_dir)
    return p4_file, target_dir


def run_z3p4_test(test_name):
    p4_file, target_dir = prep_test(test_name)
    result = p4c_check.validate_translation(p4_file, target_dir, P4C_BIN)
    if result == util.EXIT_SKIPPED:
        pytest.skip(f"Skipping file {p4_file}.")
    return result


# ***** working tests *****
bmv2_tests = [
    "key-bmv2.p4",
    "issue232-bmv2.p4",
    "issue242.p4",
    "issue249.p4",
    "issue270-bmv2.p4",
    "issue272-1-bmv2.p4",
    "issue281.p4",
    "array-copy-bmv2.p4",
    "basic_routing-bmv2.p4",
    "issue1412-bmv2.p4",
    "issue323.p4",
    "issue447-3-bmv2.p4",
    "pvs-nested-struct.p4",
    "checksum1-bmv2.p4",
    "def-use.p4",
    "drop-bmv2.p4",
    "empty-bmv2.p4",
    "equality-varbit-bmv2.p4",
    "flag_lost-bmv2.p4",
    "ipv6-switch-ml-bmv2.p4",
    "issue355-bmv2.p4",
    "issue361-bmv2.p4",
    "issue447-2-bmv2.p4",
    "issue447-bmv2.p4",
    "issue486-bmv2.p4",
    "issue655-bmv2.p4",
    "issue655.p4",
    "issue692-bmv2.p4",
    "issue696-bmv2.p4",
    "issue774-4-bmv2.p4",
    "issue841.p4",
    "issue887.p4",
    "issue891-bmv2.p4",
    "issue983-bmv2.p4",
    "match-on-exprs-bmv2.p4",
    "match-on-exprs2-bmv2.p4",
    "multicast-bmv2.p4",
    "mux-bmv2.p4",
    "named_meter_1-bmv2.p4",
    "pvs-struct.p4",
    "scalarmeta-bmv2.p4",
    "stack_complex-bmv2.p4",
    "std_meta_inlining.p4",
    "strength3.p4",
    "strength4.p4",
    "subparser-with-header-stack-bmv2.p4",
    "verify-bmv2.p4",
    "x-bmv2.p4",
    "issue1079-bmv2.p4",
    "issue134-bmv2.p4",
    "issue1409-bmv2.p4",
    "issue1470-bmv2.p4",
    "issue1544-1-bmv2.p4",
    "issue1544-2-bmv2.p4",
    "issue1544-bmv2.p4",
    "issue1560-bmv2.p4",
    "issue1595.p4",
    "issue1607-bmv2.p4",
    "issue1630-bmv2.p4",
    "issue1765-bmv2.p4",
    "issue1781-bmv2.p4",
    "issue1937-2-bmv2.p4",
    "issue1937-3-bmv2.p4",
    "issue1955.p4",
    "equality-bmv2.p4",
    "issue1538.p4",
]


@pytest.mark.parametrize("test_name", bmv2_tests)
def test_bmv2(test_name):
    assert run_z3p4_test(test_name) == util.EXIT_SUCCESS


# ***** violation tests*****
violation_tests = [
    "key-bmv2",
]


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


@pytest.mark.parametrize("test_folder", violation_tests)
def test_violation(test_folder):
    assert run_violation_test(test_folder) == util.EXIT_SUCCESS


# ***** working tests but do not generate passes *****
skipped_tests = [
    "action-synth.p4",
    "arith-bmv2.p4",
    "issue272-2-bmv2.p4",
    "arith-inline-skeleton.p4",
    "arith1-bmv2.p4",
    "arith2-bmv2.p4",
    "arith3-bmv2.p4",
    "arith4-bmv2.p4",
    "arith5-bmv2.p4",
    "issue1000-bmv2.p4",
    "issue1755-1-bmv2.p4",
    "concat-bmv2.p4",
    "free-form-annotation.p4",
    "hit-expr.p4",
    "inline-bmv2.p4",
    "inline-stack-bmv2.p4",
    "inline1-bmv2.p4",
    "intrinsic-bmv2.p4",
    "issue356-bmv2.p4",
    "issue414-bmv2.p4",
    "issue422.p4",
    "issue447-1-bmv2.p4",
    "issue447-4-bmv2.p4",
    "issue496.p4",
    "issue677-bmv2.p4",
    "issue737-bmv2.p4",
    "issue914-bmv2.p4",
    "issue955.p4",
    "issue986-1-bmv2.p4",
    "issue986-bmv2.p4",
    "issue995-bmv2.p4",
    "junk-prop-bmv2.p4",
    "same_name_for_table_and_action.p4",
    "issue1043-bmv2.p4",
    "issue1062-1-bmv2.p4",
    "issue1097-2-bmv2.p4",
    "issue1097-bmv2.p4",
    "issue1291-bmv2.p4",
    "issue1406.p4",
    "issue1517-bmv2.p4",
    "issue1713-bmv2.p4",
    "issue1755-bmv2.p4",
    "issue1876.p4",
    "issue635-bmv2.p4",
    "parser-locals2.p4",
]


@pytest.mark.parametrize("test_name", skipped_tests)
def test_skipped(test_name):
    assert run_z3p4_test(test_name) == util.EXIT_SKIPPED

# ***** actual violation *****


def test_issue1863_broken():
    p4_dir = Path("violated/issue1863/")
    p4_file, target_dir = prep_test("issue1863-bmv2.p4", p4_dir)
    result = p4c_check.validate_translation(p4_file, target_dir, P4C_BIN_1863)
    assert result == util.EXIT_VIOLATION


# ***** broken tests, need fixing *****

xfails = [
    "action-two-params.p4",  # Vector arguments
    "action_profile-bmv2.p4",  # Action profile
    "action_profile_max_group_size_annotation.p4",  # Action profile
    "action_selector_shared-bmv2.p4",  # Action selector
    "action_selector_unused-bmv2.p4",  # Action selector
    "issue297-bmv2.p4",  # Action profile
    "issue298-bmv2.p4",  # register
    "issue561-2-bmv2.p4",  # header union
    "bvec-hdr-bmv2.p4",  # Vector arguments
    "bvec_union-bmv2.p4",  # Vector arguments
    "checksum2-bmv2.p4",  # parser error
    "checksum3-bmv2.p4",  # parser error
    "crc32-bmv2.p4",  # HashAlgorithm
    "fabric_20190420/fabric.p4",  # direct_counter
    "flowlet_switching-bmv2.p4",  # register
    "hash-bmv2.p4",  # externs
    "header-bool-bmv2.p4",  # type union not supported
    "header-stack-ops-bmv2.p4",
    "issue364-bmv2.p4",
    "issue383-bmv2.p4",
    "issue420.p4",
    "issue430-1-bmv2.p4",
    "issue430-bmv2.p4",
    "issue447-5-bmv2.p4",
    "issue461-bmv2.p4",
    "issue510-bmv2.p4",
    "issue512.p4",
    "issue561-1-bmv2.p4",
    "issue793.p4",
    "issue907-bmv2.p4",
    "issue949.p4",
    "named_meter_bmv2.p4",
    "newtype2.p4",
    "saturated-bmv2.p4",
    "slice-def-use.p4",
    "slice-def-use1.p4",
    "table-entries-exact-bmv2.p4",
    "table-entries-exact-ternary-bmv2.p4",
    "table-entries-lpm-bmv2.p4",
    "table-entries-priority-bmv2.p4",
    "table-entries-range-bmv2.p4",
    "table-entries-ser-enum-bmv2.p4",
    "table-entries-ternary-bmv2.p4",
    "union-valid-bmv2.p4",
    "union1-bmv2.p4",
    "union2-bmv2.p4",
    "union3-bmv2.p4",
    "union4-bmv2.p4",
    "unused-counter-bmv2.p4",
    "v1model-p4runtime-most-types1.p4",
    "v1model-special-ops-bmv2.p4",
    "issue1001-bmv2.p4",
    "issue1025-bmv2.p4",
    "issue1049-bmv2.p4",
    "issue1062-bmv2.p4",
    "issue1107.p4",
    "issue1127-bmv2.p4",
    "issue1193-bmv2.p4",
    "issue1205-bmv2.p4",
    "issue1210.p4",
    "issue1325-bmv2.p4",
    "issue1352-bmv2.p4",
    "issue1478-bmv2.p4",
    "issue1520-bmv2.p4",
    "issue1535.p4",
    "issue1566-bmv2.p4",
    "issue1566.p4",
    "issue1642-bmv2.p4",
    "issue1653-bmv2.p4",
    "issue1653-complex-bmv2.p4",
    "issue1660-bmv2.p4",
    "issue1670-bmv2.p4",
    "issue1739-bmv2.p4",
    "issue1765-1-bmv2.p4",
    "issue1768-bmv2.p4",
    "issue1814-1-bmv2.p4",
    "issue1814-bmv2.p4",
    "issue1824-bmv2.p4",
    "issue1829-4-bmv2.p4",
    "issue1834-bmv2.p4",
    "issue1879-bmv2.p4",
    "issue1882-1-bmv2.p4",
    "issue1882-bmv2.p4",
    "issue1897-bmv2.p4",
    "issue1937-1-bmv2.p4",
    "issue1989-bmv2.p4",
    "issue561-3-bmv2.p4",
    "issue561-4-bmv2.p4",
    "issue561-5-bmv2.p4",
    "issue561-6-bmv2.p4",
    "issue561-7-bmv2.p4",
    "issue561-bmv2.p4",
    "issue562-bmv2.p4",
    "p416-type-use3.p4",
    "parser_error-bmv2.p4",
    "table-entries-valid-bmv2.p4",
    "ternary2-bmv2.p4",  # action types not properly handled
    "test-parserinvalidargument-error-bmv2.p4",
    "union-bmv2.p4",
]


@pytest.mark.xfail
@pytest.mark.parametrize("test_name", xfails)
def test_xfails(test_name):
    assert run_z3p4_test(test_name) == util.EXIT_SUCCESS
