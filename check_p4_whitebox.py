import os
import glob
import argparse
import subprocess
import logging
import hashlib
from pathlib import Path

import p4z3.util as util
import check_p4_pair as z3check

log = logging.getLogger(__name__)

FILE_DIR = os.path.dirname(os.path.abspath(__file__))
P4C_BIN = FILE_DIR + "/p4c/build/p4c"
P4Z3_BIN = FILE_DIR + "/p4c/build/p4toz3"
PASS_DIR = FILE_DIR + "/validated"

PASSES = "--top4 "
PASSES += "FrontEnd,MidEnd "
# PASSES += "FrontEnd,MidEnd,PassManager "
# PASSES += "-vvvv "


def generate_p4_dump(p4c_bin, p4_file, p4_dmp_dir):
    p4_cmd = f"{p4c_bin} "
    p4_cmd += f"{PASSES} "
    p4_cmd += f"-o {p4_dmp_dir} "
    p4_cmd += f"--dump {p4_dmp_dir} {p4_file} "
    log.debug("Running dumps with command %s ", p4_cmd)
    return util.exec_process(p4_cmd)


def prune_files(p4_prune_dir, p4_passes):
    util.check_dir(p4_prune_dir)
    for p4_file in p4_passes:
        sed_cmd = "sed -r "
        sed_cmd += "\':a; s%(.*)/\\*.*\\*/%\\1%; ta; /\\/\\*/ !b; N; ba\' "
        sed_cmd += f"{p4_file} "
        sed_cmd += " | sed -r \'/^\\s*$/d\' "
        sed_cmd += f"> {p4_prune_dir}/{os.path.basename(p4_file)}"
        log.debug("Removing comments and whitespace")
        log.debug("Command: %s", sed_cmd)
        util.exec_process(sed_cmd)
    return p4_prune_dir


def diff_files(passes, pass_dir, p4_file):

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
        log.debug("Creating a diff of the file")
        log.debug("Command: %s", diff_cmd)
        util.exec_process(diff_cmd)
        if os.stat(diff_file).st_size == 0:
            os.remove(diff_file)
        else:
            after_name = f"{diff_dir}/{p4_name}_{p4_pass}{p4_file.suffix}"
            util.copy_file(pass_after, after_name)
            og_name = f"{diff_dir}/{p4_name}_original{p4_file.suffix}"
            util.copy_file(p4_file, og_name)
    return util.EXIT_SUCCESS


def run_p4_to_py(p4_file, py_file):
    cmd = P4Z3_BIN + " "
    cmd += f"{p4_file} "
    cmd += f"--output {py_file} "
    return util.exec_process(cmd)


def list_passes(p4c_bin, p4_file, p4_dmp_dir):
    p4_pass_cmd = f"{p4c_bin} -v "
    p4_pass_cmd += f"-o {p4_dmp_dir} "
    p4_pass_cmd += f"{p4_file} 2>&1 "
    p4_pass_cmd += "| sed -e '/FrontEnd\\|MidEnd/!d' | "
    # p4_pass_cmd += "| sed -e '/FrontEnd\\|MidEnd\\|PassManager/!d' | "
    p4_pass_cmd += "sed -e '/Writing program to/d' "
    log.debug("Grabbing passes with command %s", p4_pass_cmd)
    output = subprocess.check_output(p4_pass_cmd, shell=True)
    passes = output.decode('ascii').strip().split('\n')
    return passes


def gen_p4_passes(p4c_bin, p4_dmp_dir, p4_file):
    util.check_dir(p4_dmp_dir)
    # ignore the compiler output here, for now.
    result = generate_p4_dump(p4c_bin, p4_file, p4_dmp_dir)
    # log.warning(result.stderr.decode('utf-8'))
    # if result.returncode == 1:
    # return []
    p4_passes = list_passes(p4c_bin, p4_file, p4_dmp_dir)
    full_p4_passes = []
    for p4_pass in p4_passes:
        p4_name = f"{p4_file.stem}-{p4_pass}.p4i"
        full_p4_pass = p4_dmp_dir.joinpath(p4_name)
        full_p4_passes.append(full_p4_pass)
    return full_p4_passes


def prune_passes(p4_passes):
    pruned_passes = []

    def sha256(fname):
        hash_sha256 = hashlib.sha256()
        with open(fname, "rb") as f:
            for chunk in iter(lambda: f.read(4096), b""):
                hash_sha256.update(chunk)
        return hash_sha256.hexdigest()

    hash_prev = None
    for p4_pass in p4_passes:
        hash_sha256 = sha256(p4_pass)
        if hash_prev == hash_sha256:
            log.debug("Deleting file from test set:\n%s", p4_pass)
            os.remove(p4_pass)
        else:
            pruned_passes.append(p4_pass)
        hash_prev = hash_sha256
    return pruned_passes


def validate_translation(p4_file, target_dir, p4c_bin):
    log.info("\n\n" + "-" * 70)
    log.info("Analysing %s", p4_file)
    util.check_dir(target_dir)
    fail_dir = target_dir.joinpath("failed")
    # run the p4 compiler and dump all the passes for this file
    passes = gen_p4_passes(p4c_bin, target_dir, p4_file)
    passes = prune_passes(passes)
    p4_py_files = []
    # for each emitted pass, generate a python representation
    for p4_pass in passes:
        p4_path = Path(p4_pass).stem
        py_file = f"{target_dir}/{p4_path}.py"
        result = run_p4_to_py(p4_pass, py_file)
        if result.returncode != util.EXIT_SUCCESS:
            log.error("Failed to translate P4 to Python.")
            log.error("Compiler crashed!")
            util.check_dir(fail_dir)
            with open(f"{fail_dir}/error.txt", 'w+') as err_file:
                err_file.write(result.stderr.decode("utf-8"))
            util.copy_file([p4_pass, py_file], fail_dir)
            return result.returncode
        p4_py_files.append(f"{target_dir}/{p4_path}")
    if len(p4_py_files) < 2:
        log.warning("P4 file did not generate enough passes!")
        return util.EXIT_SKIPPED
    # perform the actual comparison
    result = z3check.z3_check(p4_py_files, fail_dir)
    return result


def analyse_p4_file(p4_file, pass_dir):
    p4_dmp_dir = f"dumps"
    p4_prune_dir = f"{p4_dmp_dir}/pruned"

    p4_passes = gen_p4_passes(P4C_BIN, p4_dmp_dir, p4_file)
    prune_files(p4_prune_dir, p4_passes)
    err = diff_files(p4_passes, pass_dir, p4_file)
    util.del_dir(p4_dmp_dir)
    return err


def generate_analysis():

    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--p4_input", dest="p4_input",
                        default="p4c/testdata/p4_16_samples",
                        help="A P4 file or path to a "
                        "directory which contains P4 files.")
    # Parse options and process argv
    args = parser.parse_args()
    p4_input = args.p4_input
    if os.path.isfile(p4_input):
        pass_dir = "single_passes"
        util.check_dir(pass_dir)
        open(f"{pass_dir}/no_passes.txt", 'w+')
        analyse_p4_file(p4_input, pass_dir)
    else:
        pass_dir = "passes"
        util.check_dir(pass_dir)
        open(f"{pass_dir}/no_passes.txt", 'w+')
        for p4_file in glob.glob(f"{p4_input}/*.p4i"):
            analyse_p4_file(p4_file, pass_dir)


def main(args):

    p4_input = Path(args.p4_input)
    pass_dir = Path(args.pass_dir)
    p4c_bin = args.p4c_bin
    if os.path.isfile(p4_input):
        pass_dir = pass_dir.joinpath(p4_input.stem)
        util.del_dir(pass_dir)
        result = validate_translation(p4_input, pass_dir, p4c_bin)
        exit(result)
    else:
        util.check_dir(pass_dir)
        for p4_file in list(p4_input.glob("**/*.p4")):
            output_dir = pass_dir.joinpath(p4_file.stem)
            util.del_dir(output_dir)
            result = validate_translation(p4_file, output_dir, p4c_bin)
    exit(util.EXIT_SUCCESS)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--p4_input", dest="p4_input",
                        default="p4c/testdata/p4_16_samples",
                        required=True,
                        help="A P4 file or path to a "
                        "directory which contains P4 files.")
    parser.add_argument("-o", "--out_dir", dest="pass_dir",
                        default=PASS_DIR,
                        help="The output folder where all passes are dumped.")
    parser.add_argument("-p", "--p4c_bin", dest="p4c_bin",
                        default=P4C_BIN,
                        help="Specifies the p4c binary to compile a p4 file.")
    parser.add_argument("-l", "--log_file", dest="log_file",
                        default="analysis.log",
                        help="Specifies name of the log file.")
    # Parse options and process argv
    arguments = parser.parse_args()

    # configure logging
    logging.basicConfig(filename=arguments.log_file,
                        format="%(levelname)s:%(message)s",
                        level=logging.INFO,
                        filemode='w')
    stderr_log = logging.StreamHandler()
    stderr_log.setFormatter(logging.Formatter("%(levelname)s:%(message)s"))
    logging.getLogger().addHandler(stderr_log)
    main(arguments)
