import unittest
import os
import subprocess
from pathlib import Path
import glob
import z3_p4.util as util

# configure logging
import logging
logging.basicConfig(format="%(levelname)s:%(message)s",
                    level=logging.INFO)
log = logging.getLogger(__name__)

FILE_DIR = os.path.dirname(os.path.abspath(__file__))
P4_BINARY = FILE_DIR + "/p4c/build/p4toz3"
CHECK_BINARY = FILE_DIR + "/z3_p4/p4z3_check.py"
TARGET_DIR = FILE_DIR + "/generated"
P4_DIR = FILE_DIR + "/p4c/testdata/p4_16_samples/"
P4_BIN = FILE_DIR + "/p4c/build/p4c-bm2-ss"


def run_p4toz3(p4_file, id):
    cmd = P4_BINARY + " "
    cmd += str(p4_file) + " "
    cmd += f"--output {TARGET_DIR}/{p4_file.stem}.py "
    return util.exec_process(cmd)


def generate_p4_dump(p4_file, p4_dmp_dir):
    p4_cmd = f"{P4_BIN} "
    p4_cmd += "--top4 MidEnd "
    p4_cmd += f"--dump {p4_dmp_dir} "
    p4_cmd += p4_file
    log.debug(f"Running dumps with command {p4_cmd}")
    util.exec_process(p4_cmd)


def run_pass_dump(p4_file):
    p4_dmp_dir = f"{TARGET_DIR}/dumps"
    util.check_dir(p4_dmp_dir)
    generate_p4_dump(p4_file, p4_dmp_dir)
    p4_passes = glob.glob(f"{p4_dmp_dir}/*.p4")
    return p4_passes


class Z3Tests(unittest.TestCase):

    def validate_translation(self, p4_file):
        # run the p4 compiler and dump all the passes for this file
        passes = run_pass_dump(p4_file)
        p4_py_files = []
        # for each emitted pass, generate a python representation
        for p4_pass in passes:
            p4_py_file = Path(p4_pass)
            result = run_p4toz3(p4_py_file, 1)
            self.assertEqual(result.returncode, util.EXIT_SUCCESS)
            p4_py_files.append(p4_py_file)

        # perform the actual comparison
        cmd = f"python3 {CHECK_BINARY} "
        cmd += "--progs "
        for p4_py_file in p4_py_files:
            cmd += f"{TARGET_DIR}/{p4_py_file.stem} "
        result = util.exec_process(cmd)
        self.assertEqual(result.returncode, util.EXIT_SUCCESS)

    def setUp(self):
        util.del_dir(TARGET_DIR)
        util.check_dir(TARGET_DIR)

    def test_key_bmv2(self):
        p4_file = f"{P4_DIR}/key-bmv2.p4"
        self.validate_translation(p4_file)

    def test_strength3(self):
        p4_file = f"{P4_DIR}/strength3.p4"
        self.validate_translation(p4_file)

    def test_issue_1544(self):
        p4_file = f"{P4_DIR}/issue1544-bmv2.p4"
        self.validate_translation(p4_file)

    def test_basic_routing_bmv2(self):
        p4_file = f"{P4_DIR}/basic_routing-bmv2.p4"
        self.validate_translation(p4_file)


if __name__ == '__main__':
    unittest.main()
