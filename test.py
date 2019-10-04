import unittest
import os
import logging

import p4z3.util as util
import pass_analysis as pa

# configure logging
logging.basicConfig(format="%(levelname)s:%(message)s",
                    level=logging.INFO)
log = logging.getLogger(__name__)

FILE_DIR = os.path.dirname(os.path.abspath(__file__))
TARGET_DIR = FILE_DIR + "/generated"
P4_DIR = FILE_DIR + "/p4c/testdata/p4_16_samples/"

P4C_BIN = FILE_DIR + "/p4c_bins/latest"
P4C_BIN_1863 = FILE_DIR + "/p4c_bins/issue1863"


class Z3Tests(unittest.TestCase):

    def setUp(self):
        util.del_dir(TARGET_DIR)
        util.check_dir(TARGET_DIR)

    def test_key_bmv2(self):
        p4_file = f"{P4_DIR}/key-bmv2.p4"
        result = pa.validate_translation(p4_file, TARGET_DIR, P4C_BIN)
        self.assertEqual(result, util.EXIT_SUCCESS)

    def test_strength3(self):
        p4_file = f"{P4_DIR}/strength3.p4"
        result = pa.validate_translation(p4_file, TARGET_DIR, P4C_BIN)
        self.assertEqual(result, util.EXIT_SUCCESS)

    def test_issue1544(self):
        p4_file = f"{P4_DIR}/issue1544-bmv2.p4"
        result = pa.validate_translation(p4_file, TARGET_DIR, P4C_BIN)
        self.assertEqual(result, util.EXIT_SUCCESS)

    # actual violation
    def test_issue1863(self):
        p4_file = f"p4z3/p4files/issue1863/issue1863-bmv2.p4"
        result = pa.validate_translation(p4_file, TARGET_DIR, P4C_BIN_1863)
        self.assertNotEqual(result, util.EXIT_SUCCESS)

    # broken tests
    def test_issue1595(self):
        p4_file = f"{P4_DIR}/issue1595.p4"
        result = pa.validate_translation(p4_file, TARGET_DIR, P4C_BIN)
        self.assertNotEqual(result, util.EXIT_SUCCESS)

    def test_basic_routing_bmv2(self):
        p4_file = f"{P4_DIR}/basic_routing-bmv2.p4"
        result = pa.validate_translation(p4_file, TARGET_DIR, P4C_BIN)
        self.assertNotEqual(result, util.EXIT_SUCCESS)

    def test_equality_bmv2(self):
        p4_file = f"{P4_DIR}/equality-bmv2.p4"
        result = pa.validate_translation(p4_file, TARGET_DIR, P4C_BIN)
        self.assertNotEqual(result, util.EXIT_SUCCESS)

    def test_issue983(self):
        p4_file = f"{P4_DIR}/issue983-bmv2.p4"
        result = pa.validate_translation(p4_file, TARGET_DIR, P4C_BIN)
        self.assertNotEqual(result, util.EXIT_SUCCESS)


if __name__ == '__main__':
    unittest.main(failfast=True)
