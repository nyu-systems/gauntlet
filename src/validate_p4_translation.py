import os
import sys
import json
import argparse
import subprocess
import logging
import hashlib
import time
from datetime import datetime

from pathlib import Path

import p4z3.util as util
import check_p4_pair as z3check

log = logging.getLogger(__name__)

FILE_DIR = Path(__file__).parent.resolve()
P4C_BIN = FILE_DIR.joinpath("../modules/p4c/build/p4test")
P4Z3_BIN = FILE_DIR.joinpath("../modules/p4c/build/p4toz3")
PASS_DIR = FILE_DIR.joinpath("../validated")


PASSES = "--top4 "
PASSES += "FrontEnd,MidEnd,PassManager "
# PASSES += "FrontEnd,MidEnd,PassManager "
# PASSES += "-vvvv "
# passes with "::" in them are a little bit funky.. ignore those
# this emits all passes, but that is too much right now...
# PASSES += "\"^(?!.*::.*).*\" "

INFO = {"compiler": str(P4C_BIN),
        "exit_code": util.EXIT_SUCCESS,
        "prog_before": "",
        "prog_after": "",
        "p4z3_bin": str(P4Z3_BIN),
        "out_dir": str(PASS_DIR),
        "input_file": "",
        "allow_undef": False,
        "validation_bin": f"python3 {__file__}",
        "err_string": "",
        }


def generate_p4_dump(p4c_bin, p4_file, p4_dmp_dir):
    p4_cmd = f"{p4c_bin} "
    p4_cmd += f"{PASSES} "
    # p4_cmd += f"-o {p4_dmp_dir} "
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
        sed_cmd += f"> {p4_prune_dir}/{p4_file.name}"
        log.debug("Removing comments and whitespace")
        log.debug("Command: %s", sed_cmd)
        util.exec_process(sed_cmd)
    return p4_prune_dir


def diff_files(passes, pass_dir, p4_file):

    p4_name = p4_file.name.stem
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
    cmd = f"{P4Z3_BIN} "
    cmd += f"{p4_file} "
    cmd += f"--output {py_file} "
    return util.exec_process(cmd)


def list_passes(p4c_bin, p4_file, p4_dmp_dir):
    p4_pass_cmd = f"{p4c_bin} -v "
    # p4_pass_cmd += f"-o {p4_dmp_dir} "
    p4_pass_cmd += f"{p4_file} 2>&1 "
    # p4_pass_cmd += "| sed -e '/FrontEnd\\|MidEnd/!d' | "
    p4_pass_cmd += "| sed -e '/FrontEnd\\|MidEnd\\|PassManager/!d' | "
    p4_pass_cmd += "sed -e '/Writing program to/d' "
    # p4_pass_cmd += "| grep 'Writing program to' "
    # p4_pass_cmd += "| sed -e 's/Writing program to //g' "
    log.debug("Grabbing passes with command %s", p4_pass_cmd)
    output = subprocess.check_output(p4_pass_cmd, shell=True)
    if output:
        return output.decode('ascii').strip().split('\n')
    # return an empty list if no pass is used
    return []


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
        p4_name = f"{p4_file.stem}-{p4_pass}.p4"
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


def validate_translation(p4_file, target_dir, p4c_bin,
                         allow_undef=False, dump_info=False):
    info = INFO

    # customize the main info with the new information
    info["compiler"] = str(p4c_bin)
    info["exit_code"] = util.EXIT_SUCCESS
    info["p4z3_bin"] = str(P4Z3_BIN)
    info["out_dir"] = str(target_dir)
    info["input_file"] = str(p4_file)
    info["allow_undef"] = allow_undef
    info["validation_bin"] = f"python3 {__file__}"

    log.info("\n" + "-" * 70)
    log.info("Analysing %s", p4_file)
    start_time = datetime.now()
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
    result, check_info = z3check.z3_check(p4_py_files, fail_dir, allow_undef)
    # merge the two info dicts
    info["exit_code"] = result
    info = {**info, **check_info}
    done_time = datetime.now()
    elapsed = done_time - start_time
    time_str = time.strftime("%H hours %M minutes %S seconds",
                             time.gmtime(elapsed.total_seconds()))
    ms = elapsed.microseconds / 1000
    log.info("Translation validation took %s %s milliseconds.",
             time_str, ms)
    if dump_info:
        json_name = target_dir.joinpath(f"{p4_file.stem}_info.json")
        log.info("Dumping configuration to %s.", json_name)
        with open(json_name, 'w') as json_file:
            json.dump(info, json_file, indent=2, sort_keys=True)
    return result


def main(args):

    p4_input = Path(args.p4_input).resolve()
    pass_dir = Path(args.pass_dir)
    p4c_bin = args.p4c_bin
    allow_undef = args.allow_undef
    dunp_info = args.dunp_info
    if os.path.isfile(p4_input):
        pass_dir = pass_dir.joinpath(p4_input.stem)
        util.del_dir(pass_dir)
        result = validate_translation(
            p4_input, pass_dir, p4c_bin, allow_undef, dunp_info)
        sys.exit(result)
    elif os.path.isdir(p4_input):
        util.check_dir(pass_dir)
        for p4_file in list(p4_input.glob("**/*.p4")):
            output_dir = pass_dir.joinpath(p4_file.stem)
            util.del_dir(output_dir)
            validate_translation(
                p4_file, output_dir, p4c_bin, allow_undef)
        result = util.EXIT_SUCCESS
    else:
        log.error("Input file \"%s\" does not exist!", p4_input)
        result = util.EXIT_SUCCESS
    sys.exit(result)


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
    parser.add_argument("-u", "--allow_undefined", dest="allow_undef",
                        action="store_true",
                        help="Ignore changes in undefined behavior.")
    parser.add_argument("-l", "--log_file", dest="log_file",
                        default="analysis.log",
                        help="Specifies name of the log file.")
    parser.add_argument("-d", "--dump_info", dest="dunp_info",
                        action="store_true",
                        help="Dump an informative JSON file in"
                             " the output directory.")
    parser.add_argument("-ll", "--log_level", dest="log_level",
                        default="INFO",
                        choices=["CRITICAL", "ERROR", "WARNING",
                                 "INFO", "DEBUG", "NOTSET"],
                        help="The log level to choose.")
    # Parse options and process argv
    arguments = parser.parse_args()
    # configure logging
    logging.basicConfig(filename=arguments.log_file,
                        format="%(levelname)s:%(message)s",
                        level=getattr(logging, arguments.log_level),
                        filemode='w')
    stderr_log = logging.StreamHandler()
    stderr_log.setFormatter(logging.Formatter("%(levelname)s:%(message)s"))
    logging.getLogger().addHandler(stderr_log)
    main(arguments)
