import unittest
import os
import subprocess
import logging as log
from pathlib import Path


FILE_DIR = os.path.dirname(os.path.abspath(__file__))

P4_BINARY = FILE_DIR + "/../p4c/build/p4toz3"


def exec_process(cmd, out_file=subprocess.STDOUT):
    log.debug("Executing %s " % cmd)
    if out_file is subprocess.STDOUT:
        result = subprocess.run(
            cmd.split(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.stdout:
            log.debug("Process output: %s" % result.stdout)
        if result.stderr and result.returncode != 0:
            log.error(result.stderr)
        return result
    err = out_file + ".err"
    out = out_file + ".out"
    with open(out, "w+") as f_out, open(err, "w+") as f_err:
        return subprocess.run(cmd.split(), stdout=f_out, stderr=f_err)


def run_p4toz3(p4_file, id):
    cmd = P4_BINARY + " "
    cmd += str(p4_file) + " "
    cmd += f"--output generated/{p4_file.stem}.py "
    return exec_process(cmd)


def check_dir(directory):
    # create the folder if it does not exit
    if not directory == "" and not os.path.exists(directory):
        log.debug(f"Folder {directory} does not exist! Creating...")
        os.makedirs(directory)
        # preserve the original owner


class Z3Tests(unittest.TestCase):

    def test_key_bmv2(self):
        check_dir("generated")
        p4_file_0 = Path(f"{FILE_DIR}/p4files/key-bmv2/key-bmv2-frontend.p4")
        result = run_p4toz3(p4_file_0, 0)
        self.assertEqual(result.returncode, 0)
        p4_file_1 = Path(f"{FILE_DIR}/p4files/key-bmv2/key-bmv2_8_SimplifyKey.p4")
        result = run_p4toz3(p4_file_1, 1)
        self.assertEqual(result.returncode, 0)
        result = exec_process(f"python3 p4z3_check.py --progs generated/key-bmv2-frontend generated/key-bmv2_8_SimplifyKey")
        print(result)
        self.assertEqual(result.returncode, 0)


if __name__ == '__main__':
    unittest.main()
