import unittest
import os
import subprocess
from pathlib import Path
import glob
import p4z3.util as util
import pass_analysis as pa

# configure logging
import logging
logging.basicConfig(format="%(levelname)s:%(message)s",
                    level=logging.INFO)
log = logging.getLogger(__name__)

FILE_DIR = os.path.dirname(os.path.abspath(__file__))
TARGET_DIR = FILE_DIR + "/generated"
P4_DIR = FILE_DIR + "/p4c/testdata/p4_16_samples/"


def validate_p4_prog(p4_file):
    return pa.validate_translation(p4_file, TARGET_DIR)


class Z3Tests(unittest.TestCase):

    def setUp(self):
        util.del_dir(TARGET_DIR)
        util.check_dir(TARGET_DIR)

    def test_key_bmv2(self):
        p4_file = f"{P4_DIR}/key-bmv2.p4"
        self.assertEqual(validate_p4_prog(p4_file), util.EXIT_SUCCESS)

    def test_strength3(self):
        p4_file = f"{P4_DIR}/strength3.p4"
        self.assertEqual(validate_p4_prog(p4_file), util.EXIT_SUCCESS)

    def test_issue_1544(self):
        p4_file = f"{P4_DIR}/issue1544-bmv2.p4"
        self.assertEqual(validate_p4_prog(p4_file), util.EXIT_SUCCESS)

    # broken tests
    def test_issue1595(self):
        p4_file = f"{P4_DIR}/issue1595.p4"
        self.assertNotEqual(validate_p4_prog(p4_file), util.EXIT_SUCCESS)

    def test_issue1863(self):
        p4_file = f"{P4_DIR}/issue1863.p4"
        self.assertNotEqual(validate_p4_prog(p4_file), util.EXIT_SUCCESS)

    def test_basic_routing_bmv2(self):
        p4_file = f"{P4_DIR}/basic_routing-bmv2.p4"
        self.assertNotEqual(validate_p4_prog(p4_file), util.EXIT_SUCCESS)

    def test_equality_bmv2(self):
        p4_file = f"{P4_DIR}/equality-bmv2.p4"
        self.assertNotEqual(validate_p4_prog(p4_file), util.EXIT_SUCCESS)

    def test_issue983(self):
        p4_file = f"{P4_DIR}/issue983-bmv2.p4"
        self.assertNotEqual(validate_p4_prog(p4_file), util.EXIT_SUCCESS)


if __name__ == '__main__':
    unittest.main(failfast=True)
