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
    "hit-expr.p4",
    "concat-bmv2.p4",
]


@pytest.mark.parametrize("test_name", bmv2_tests)
def test_bmv2(test_name):
    assert run_z3p4_test(test_name) == util.EXIT_SUCCESS

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
    "array-copy-bmv2.p4",  # header stacks not implemented
    "drop-bmv2.p4",  # pass by reference still broken...
]


@pytest.mark.xfail
@pytest.mark.parametrize("test_name", xfails)
def test_xfails(test_name):
    assert run_z3p4_test(test_name) == util.EXIT_SUCCESS
