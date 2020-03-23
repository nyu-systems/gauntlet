import random
import string
import logging
import argparse
from multiprocessing import Pool
from functools import wraps
import errno
import os
import signal

from pathlib import Path
import p4z3.util as util


# configure logging
log = logging.getLogger(__name__)

FILE_DIR = Path(__file__).parent.resolve()
P4C_BIN = FILE_DIR.joinpath("p4c/build/p4c")
TOFINO_BIN = FILE_DIR.joinpath("tofino/bf_src/install/bin/bf-p4c")
P4Z3_BIN = FILE_DIR.joinpath("p4c/build/p4toz3")
P4RANDOM_BIN = FILE_DIR.joinpath("p4c/build/p4bludgeon")

OUTPUT_DIR = FILE_DIR.joinpath("random")
GENERATOR_BUG_DIR = OUTPUT_DIR.joinpath("generator_bugs")
CRASH_BUG_DIR = OUTPUT_DIR.joinpath("crash_bugs")
VALIDATION_BUG_DIR = OUTPUT_DIR.joinpath("validation_bugs")
TIMEOUT_DIR = OUTPUT_DIR.joinpath("timeout_bugs")
ITERATIONS = 10000
NUM_PROCESSES = 4
USE_EMI = False
USE_TOFINO = False
DO_VALIDATE = False

KNOWN_BUGS = [
    "Conditional execution",
    "Unimplemented compiler support",
    "width of left operand of shift needs to be specified",
    # bf
    "Unsupported on target",
    "Unsupported action spanning multiple stages",
    "shift count must be",
    "Null cst",
    "no definitions",
    "condition too complex",
    "source of modify_field invalid",
    "Please consider simplifying",
    "Operands of arithmetic operations cannot be greater",
    "ListCompileTimeValue",
    "does not appear on the hash function",
    "Match group map doesn't match format size",
    "operating on container ",
]


def timeout(seconds=10, error_message=os.strerror(errno.ETIME)):
    def decorator(func):
        def _handle_timeout(signum, frame):
            raise TimeoutError(error_message)

        def wrapper(*args, **kwargs):
            signal.signal(signal.SIGALRM, _handle_timeout)
            signal.alarm(seconds)
            try:
                result = func(*args, **kwargs)
            finally:
                signal.alarm(0)
            return result

        return wraps(func)(wrapper)

    return decorator


def generate_id():
    # try to generate a valid C identifier
    # first letter cannot be a number
    sw_id = random.choice(string.ascii_letters)
    appendix = [random.choice(
        string.ascii_letters + string.digits) for ch in range(4)]
    sw_id += "".join(appendix)
    return sw_id


def generate_p4_dump(p4c_bin, p4_file):
    p4_cmd = f"{p4c_bin} "
    p4_cmd += f"{p4_file} "
    if USE_TOFINO:
        p4_cmd += f"1 "
    else:
        p4_cmd += f"0 "
    log.debug("Generating random p4 code with command %s ", p4_cmd)
    return util.exec_process(p4_cmd), p4_file


def compile_p4_prog(p4c_bin, p4_file, p4_dump_dir):
    p4_cmd = f"{p4c_bin} "
    # p4_cmd += f"-vvvv "
    p4_cmd += f"{p4_file} "
    p4_cmd += f"-o  {p4_dump_dir}"
    log.debug("Checking compilation with command %s ", p4_cmd)
    return util.exec_process(p4_cmd)


def dump_result(result, target_dir, p4_file):
    util.check_dir(target_dir)
    test_id = target_dir.joinpath(p4_file.stem)
    with open(f"{test_id}.err", 'w+') as err_file:
        err_file.write(result.stderr.decode("utf-8"))


def dump_file(target_dir, p4_file):
    util.check_dir(target_dir)
    target = target_dir.joinpath(p4_file.name)
    p4_file.rename(target)


def is_known_bug(result):
    for bug in KNOWN_BUGS:
        if bug in result.stderr.decode("utf-8"):
            log.info("Error \"%s\" already known. Skipping...", bug)
            return True
    return False


@timeout(seconds=600)
def validate_p4(p4_file, target_dir, p4c_bin, log_file):
    p4z3_cmd = "python3 check_p4_compilation.py "
    p4z3_cmd += f"-i {p4_file} "
    p4z3_cmd += f"-o {target_dir} "
    p4z3_cmd += f"-p {p4c_bin} "
    p4z3_cmd += f"-l {log_file} "
    return util.exec_process(p4z3_cmd)


@timeout(seconds=600)
def validate_p4_emi(p4_file, target_dir, log_file):
    p4z3_cmd = "python3 check_p4_emi.py "
    p4z3_cmd += f"-i {p4_file} "
    p4z3_cmd += f"-o {target_dir} "
    p4z3_cmd += f"-l {log_file} "
    if USE_TOFINO:
        p4z3_cmd += f"-t "
    return util.exec_process(p4z3_cmd)


def validate(dump_dir, p4_file, log_file):
    try:
        # Tofino does not allow insights into the individual passes
        # So we are forced to use the EMI technique
        if USE_EMI or USE_TOFINO:
            result = validate_p4_emi(p4_file, dump_dir, log_file)
        else:
            result = validate_p4(p4_file, dump_dir, P4C_BIN, log_file)
    except TimeoutError:
        log.error("Validation timed out.")
        dump_file(TIMEOUT_DIR, p4_file)
        dump_file(TIMEOUT_DIR, log_file)
        # reset the dump directory
        return util.EXIT_FAILURE
    if result.returncode != util.EXIT_SUCCESS:
        log.error("Failed to validate the P4 code!")
        log.error("Rerun the example with:")
        out_file = VALIDATION_BUG_DIR.joinpath(p4_file.name)
        if USE_TOFINO:
            err_log = dump_dir.joinpath(Path(p4_file.stem + "_ptf_err.log"))
            dump_file(VALIDATION_BUG_DIR, err_log)
        if USE_EMI:
            log.error("python3 check_p4_emi.py -i %s", out_file)
            stf_name = dump_dir.joinpath(Path(p4_file.stem + ".stf"))
            dump_file(VALIDATION_BUG_DIR, stf_name)
        else:
            log.error("python3 check_p4_compilation.py -i %s", out_file)
        dump_file(VALIDATION_BUG_DIR, log_file)
        dump_file(VALIDATION_BUG_DIR, p4_file)
    return result.returncode


def check(idx):
    test_id = generate_id()
    test_name = f"{test_id}_{idx}"
    dump_dir = OUTPUT_DIR.joinpath(f"dmp_{test_name}")
    util.check_dir(dump_dir)
    log_file = dump_dir.joinpath(f"{test_name}.log")
    p4_file = dump_dir.joinpath(f"{test_name}.p4")
    log.info("Testing p4 program %s", p4_file)
    # generate a random program
    result, p4_file = generate_p4_dump(P4RANDOM_BIN, p4_file)
    if result.returncode != util.EXIT_SUCCESS:
        log.error("Failed generate P4 code!")
        dump_result(result, GENERATOR_BUG_DIR, p4_file)
        # reset the dump directory
        util.del_dir(dump_dir)
        return result.returncode
    # check compilation
    if USE_TOFINO:
        result = compile_p4_prog(TOFINO_BIN, p4_file, dump_dir)
    else:
        result = compile_p4_prog(P4C_BIN, p4_file, dump_dir)
    if result.returncode != util.EXIT_SUCCESS:
        if not is_known_bug(result):
            log.error("Failed to compile the P4 code!")
            log.error("Found a new bug!")
            dump_result(result, CRASH_BUG_DIR, p4_file)
            dump_file(CRASH_BUG_DIR, p4_file)
        # reset the dump directory
        util.del_dir(dump_dir)
        return result
    # check validation
    if DO_VALIDATE:
        result = validate(dump_dir, p4_file, log_file)
    # reset the dump directory
    util.del_dir(dump_dir)
    return result


def main(args):
    util.check_dir(OUTPUT_DIR)
    if USE_TOFINO and DO_VALIDATE:
        # tofino only supports single threaded mode for now
        for idx in range(ITERATIONS):
            check(idx)
        return
    with Pool(NUM_PROCESSES) as p:
        p.map(check, range(ITERATIONS))
    return


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--use-emi", "-e", dest="use_emi", action='store_true',
                        help="Use an EMI-like technique instead of translation"
                        "validation.")
    parser.add_argument("--use-tofino", "-t", dest="use_tofino",
                        action='store_true',
                        help="Use the Tofino backend instead of BMV2.")
    parser.add_argument("-l", "--log_file", dest="log_file",
                        default="random.log",
                        help="Specifies name of the log file.")
    parser.add_argument("-v", "--validate", dest="do_validate",
                        action='store_true',
                        help="Also perform validation on programs.")
    # Parse options and process argv
    args = parser.parse_args()
    # lazy hack because I do not want to write a wrapper for map()
    USE_EMI = args.use_emi
    USE_TOFINO = args.use_tofino
    DO_VALIDATE = args.do_validate
    # configure logging
    logging.basicConfig(filename=args.log_file,
                        format="%(levelname)s:%(message)s",
                        level=logging.INFO,
                        filemode='w')
    stderr_log = logging.StreamHandler()
    stderr_log.setFormatter(logging.Formatter("%(levelname)s:%(message)s"))
    log.addHandler(stderr_log)
    main(args)
