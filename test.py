import os
import logging

import pytest
from pathlib import Path
import p4z3.util as util
import pass_analysis as pa

# configure logging
logging.basicConfig(format="%(levelname)s:%(message)s",
                    level=logging.INFO)
log = logging.getLogger(__name__)

FILE_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
TARGET_DIR = FILE_DIR.joinpath("generated")
P4_DIR = FILE_DIR.joinpath("p4c/testdata/p4_16_samples/")

P4C_BIN = FILE_DIR.joinpath("p4c/build/p4c-bm2-ss")
P4C_BIN_1863 = FILE_DIR.joinpath("p4c_bins/issue1863")


def prep_test(p4_name):
    p4_file = P4_DIR.joinpath(p4_name)
    target_dir = TARGET_DIR.joinpath(p4_file.stem)
    util.del_dir(target_dir)
    util.check_dir(target_dir)
    return p4_file, target_dir


# ***** working tests *****

def test_key_bmv2():
    p4_file, target_dir = prep_test("key-bmv2.p4")
    result = pa.validate_translation(p4_file, target_dir, P4C_BIN)
    assert result == util.EXIT_SUCCESS


def test_strength3():
    p4_file, target_dir = prep_test("strength3.p4")
    result = pa.validate_translation(p4_file, target_dir, P4C_BIN)
    assert result == util.EXIT_SUCCESS


def test_issue_1544():
    p4_file, target_dir = prep_test("issue1544-bmv2.p4")
    result = pa.validate_translation(p4_file, target_dir, P4C_BIN)
    assert result == util.EXIT_SUCCESS


def test_issue983():
    p4_file, target_dir = prep_test("issue983-bmv2.p4")
    result = pa.validate_translation(p4_file, target_dir, P4C_BIN)
    assert result == util.EXIT_SUCCESS


def test_basic_routing_bmv2():
    p4_file, target_dir = prep_test("basic_routing-bmv2.p4")
    result = pa.validate_translation(p4_file, target_dir, P4C_BIN)
    assert result == util.EXIT_SUCCESS


def test_issue1595():
    p4_file, target_dir = prep_test("issue1595.p4")
    result = pa.validate_translation(p4_file, target_dir, P4C_BIN)
    assert result == util.EXIT_SUCCESS


# ***** actual violation *****

def test_issue1863_broken():
    p4_file, target_dir = prep_test("p4z3/p4files/issue1863/issue1863-bmv2.p4")
    result = pa.validate_translation(p4_file, target_dir, P4C_BIN_1863)
    assert result == util.EXIT_FAILURE


# ***** broken tests, need fixing *****

@pytest.mark.xfail
def test_issue1863():
    # Struct initializer not implemented
    p4_file, target_dir = prep_test("issue1863.p4")
    result = pa.validate_translation(p4_file, target_dir, P4C_BIN)
    assert result == util.EXIT_SUCCESS


@pytest.mark.xfail
def test_equality_bmv2():
    # Header Stacks not implemented
    p4_file, target_dir = prep_test("equality-bmv2.p4")
    result = pa.validate_translation(p4_file, target_dir, P4C_BIN)
    assert result == util.EXIT_SUCCESS
