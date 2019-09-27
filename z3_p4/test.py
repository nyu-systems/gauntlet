import unittest
import os
import subprocess
import logging as log
import util
from pathlib import Path

FILE_DIR = os.path.dirname(os.path.abspath(__file__))
P4_BINARY = FILE_DIR + "/../p4c/build/p4toz3"
TARGET_DIR = FILE_DIR + "/generated"
P4_DIR = FILE_DIR + "/p4files"


def run_p4toz3(p4_file, id):
    cmd = P4_BINARY + " "
    cmd += str(p4_file) + " "
    cmd += f"--output {TARGET_DIR}/{p4_file.stem}.py "
    return util.exec_process(cmd)


class Z3Tests(unittest.TestCase):

    def setUp(self):
        util.check_dir(TARGET_DIR)

    def test_key_bmv2(self):
        # generate code for file 1
        p4_file_0 = Path(f"{P4_DIR}/key-bmv2/key-bmv2-frontend.p4")
        result = run_p4toz3(p4_file_0, 0)
        self.assertEqual(result.returncode, util.EXIT_SUCCESS)

        # generate code for file 2
        p4_file_1 = Path(f"{P4_DIR}/key-bmv2/key-bmv2_8_SimplifyKey.p4")
        result = run_p4toz3(p4_file_1, 1)
        self.assertEqual(result.returncode, util.EXIT_SUCCESS)

        # perform the actual comparison
        cmd = "python3 p4z3_check.py "
        cmd += "--progs "
        cmd += f"{TARGET_DIR}/{p4_file_0.stem} "
        cmd += f"{TARGET_DIR}/{p4_file_1.stem} "
        result = util.exec_process(cmd)
        self.assertEqual(result.returncode, util.EXIT_SUCCESS)


if __name__ == '__main__':
    unittest.main()
