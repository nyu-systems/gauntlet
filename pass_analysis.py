import os
import glob
import shutil
import argparse
import subprocess
import signal
from pathlib import Path

import p4z3.util as util
import p4z3_check as z3check

# configure logging
import logging
logging.basicConfig(format="%(levelname)s:%(message)s",
                    level=logging.INFO)
log = logging.getLogger(__name__)

FILE_DIR = os.path.dirname(os.path.abspath(__file__))
P4_BIN = FILE_DIR + "/p4c/build/p4c-bm2-ss"
P4Z3_BIN = FILE_DIR + "/p4c/build/p4toz3"


def generate_p4_dump(p4_file, p4_dmp_dir):
    p4_cmd = f"{P4_BIN} "
    p4_cmd += "-vvvv --top4 MidEnd "
    # disable midend for now
    # p4_cmd += "--top4 FrontEnd,MidEnd "
    p4_cmd += f"--dump {p4_dmp_dir} "
    p4_cmd += p4_file
    log.debug(f"Running dumps with command {p4_cmd}")
    return util.exec_process(p4_cmd)


def prune_files(p4_prune_dir, p4_passes):
    util.check_dir(p4_prune_dir)
    for p4_file in p4_passes:
        sed_cmd = "sed -r "
        sed_cmd += "\':a; s%(.*)/\\*.*\\*/%\\1%; ta; /\\/\\*/ !b; N; ba\' "
        sed_cmd += f"{p4_file} "
        sed_cmd += " | sed -r \'/^\\s*$/d\' "
        sed_cmd += f"> {p4_prune_dir}/{os.path.basename(p4_file)}"
        log.debug(f"Removing comments and whitespace")
        log.debug(f"Command: {sed_cmd}")
        util.exec_process(sed_cmd)
    return p4_prune_dir


def diff_files(passes, pass_dir, p4_prune_dir, p4_file):

    p4_name = Path(os.path.basename(p4_file)).stem
    for index, p4_pass in enumerate(passes[1:]):
        pass_before = passes[index - 1]
        pass_after = passes[index]
        diff_dir = f"{pass_dir}/{p4_name}"
        util.check_dir(diff_dir)
        diff_file = f"{diff_dir}/{p4_name}_{p4_pass}.diff"
        diff_cmd = "diff -rupP "
        diff_cmd += "--label=\"before_pass\" --label=\"after_pass\" "
        diff_cmd += f"{pass_before} {pass_after}"
        diff_cmd += f"> {diff_file}"
        log.debug(f"Creating a diff of the file")
        log.debug(f"Command: {diff_cmd}")
        util.exec_process(diff_cmd)
        if os.stat(diff_file).st_size == 0:
            os.remove(diff_file)
        else:
            util.copy_file(pass_after, f"{diff_dir}/{p4_name}_{p4_pass}.p4")
            util.copy_file(p4_file, f"{diff_dir}/{p4_name}_original.p4")
    return util.EXIT_SUCCESS


def list_passes(p4_file):
    p4_pass_cmd = f"{P4_BIN} -v "
    p4_pass_cmd += f"{p4_file} 2>&1 "
    p4_pass_cmd += "| sed -e \'/FrontEnd_0_/,$!d\' | "
    p4_pass_cmd += "sed -e \'/MidEndLast/q\' "
    log.debug(f"Grabbing passes with command {p4_pass_cmd}")
    output = subprocess.check_output(p4_pass_cmd, shell=True)
    passes = output.decode('ascii').strip().split('\n')
    return passes


def analyse_p4_file(p4_file, pass_dir):
    p4_dmp_dir = f"dumps"
    p4_prune_dir = f"{p4_dmp_dir}/pruned"

    log.info(f"Analysing {p4_file}")
    ir_passes = list_passes(p4_file)
    p4_passes = gen_p4_passes(p4_dmp_dir, p4_file)
    prune_files(p4_prune_dir, p4_passes)
    err = diff_files(p4_passes, pass_dir, p4_prune_dir, p4_file)
    util.del_dir(p4_dmp_dir)
    return err


def run_p4_to_py(target_dir, p4_file, py_file):
    cmd = P4Z3_BIN + " "
    cmd += p4_file + " "
    cmd += f"--output {py_file} "
    result = util.exec_process(cmd)
    return result.returncode


def gen_p4_passes(p4_dmp_dir, p4_file):
    util.check_dir(p4_dmp_dir)
    generate_p4_dump(p4_file, p4_dmp_dir)
    p4_passes = glob.glob(f"{p4_dmp_dir}/*.p4")
    # Sort the pass list before returning
    # TODO: Find a better way to maintain order
    return util.natural_sort(p4_passes)


def validate_translation(p4_file, target_dir):
    fail_dir = f"{target_dir}/failed"
    # run the p4 compiler and dump all the passes for this file
    passes = gen_p4_passes(p4_dmp_dir=target_dir, p4_file=p4_file)
    p4_py_files = []
    # for each emitted pass, generate a python representation
    for p4_file in passes:
        p4_path = Path(p4_file).stem
        py_file = f"{target_dir}/{p4_path}.py"
        result = run_p4_to_py(target_dir, p4_file, py_file)
        if result != util.EXIT_SUCCESS:
            log.error("Failed to translate P4 to Python.")
            log.error("Compiler crashed!")
            util.check_dir(fail_dir)
            util.copy_file([p4_file, py_file], fail_dir)
            return result
        p4_py_files.append(f"{target_dir}/{p4_path}")
    # perform the actual comparison
    result = z3check.z3_check(p4_py_files, fail_dir)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--p4_input", dest="p4_input",
                        default="p4c/testdata/p4_16_samples",
                        help="A P4 file or path to a "
                        "directory which contains P4 files.")
    # Parse options and process argv
    args = parser.parse_args()
    p4_input = args.p4_input
    if (os.path.isfile(p4_input)):
        pass_dir = "single_passes"
        util.check_dir(pass_dir)
        open(f"{pass_dir}/no_passes.txt", 'w+')
        analyse_p4_file(p4_input, pass_dir)
    else:
        pass_dir = "passes"
        util.check_dir(pass_dir)
        open(f"{pass_dir}/no_passes.txt", 'w+')
        for p4_file in glob.glob(f"{p4_input}/*.p4"):
            analyse_p4_file(p4_file, pass_dir)


if __name__ == '__main__':
    main()
