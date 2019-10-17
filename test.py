import logging
from pathlib import Path

import pytest
import p4z3.util as util
import pass_analysis as pa

# configure logging
logging.basicConfig(format="%(levelname)s:%(message)s",
                    level=logging.INFO)
log = logging.getLogger(__name__)

# some folder definitions
FILE_DIR = Path.resolve(Path(__file__)).parent
TARGET_DIR = FILE_DIR.joinpath("generated")
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
    result = pa.validate_translation(p4_file, target_dir, P4C_BIN)
    if result == util.EXIT_SKIPPED:
        pytest.skip(f"Skipping file {p4_file}.")
    return result


# ***** working tests *****
bmv2_tests = [
    "key-bmv2.p4",
    "strength3.p4",
    "issue1544-bmv2.p4",
    "issue983-bmv2.p4",
    "basic_routing-bmv2.p4",
    "issue1595.p4",
    "drop-bmv2.p4",
    "array-copy-bmv2.p4",
    "empty-bmv2.p4",
    "def-use.p4",
    "equality-varbit-bmv2.p4",
    "checksum1-bmv2.p4",
    "flag_lost-bmv2.p4",
]


@pytest.mark.parametrize("test_name", bmv2_tests)
def test_bmv2(test_name):
    assert run_z3p4_test(test_name) == util.EXIT_SUCCESS


# ***** working tests but do not generate passes *****
skipped_tests = [
    "action-synth.p4",
    "inline-bmv2.p4",
    "arith-bmv2.p4",
    "arith1-bmv2.p4",
    "arith2-bmv2.p4",
    "arith3-bmv2.p4",
    "arith4-bmv2.p4",
    "arith5-bmv2.p4",
    "concat-bmv2.p4",
    "fabric.p4",
    "free-form-annotation.p4",
    "hit-expr.p4",
    "inline-stack-bmv2.p4",
]


@pytest.mark.parametrize("test_name", skipped_tests)
def test_skipped(test_name):
    assert run_z3p4_test(test_name) == util.EXIT_SKIPPED

# ***** actual violation *****


def test_issue1863_broken():
    p4_dir = Path("p4z3/p4files/issue1863/")
    p4_file, target_dir = prep_test("issue1863-bmv2.p4", p4_dir)
    result = pa.validate_translation(p4_file, target_dir, P4C_BIN_1863)
    assert result == util.EXIT_FAILURE


# ***** broken tests, need fixing *****

xfails = [
    "issue1863.p4",  # Struct initializer not implemented
    "equality-bmv2.p4",  # header stacks not implemented
    "action-two-params.p4",  # Vector arguments
    "action_profile-bmv2.p4",  # Action profile
    "action_profile_max_group_size_annotation.p4",  # Action profile
    "action_selector_shared-bmv2.p4",  # Action selector
    "action_selector_unused-bmv2.p4",  # Action selector
    "bvec-hdr-bmv2.p4",  # Vector arguments
    "checksum2-bmv2.p4",  # externs
    "checksum3-bmv2.p4",  # externs
    "crc32-bmv2.p4",  # externs
    "flowlet_switching-bmv2.p4",  # externs
    "hash-bmv2.p4",  # externs
    "header-bool-bmv2.p4",  # type union not supported
    "ternary2-bmv2.p4",  # action types not properly handled
]


@pytest.mark.xfail
@pytest.mark.parametrize("test_name", xfails)
def test_xfails(test_name):
    assert run_z3p4_test(test_name) == util.EXIT_SUCCESS
