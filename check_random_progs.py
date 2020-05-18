import random
import string
import logging
import argparse
from multiprocessing import Pool
from functools import wraps
import errno
import os
import signal
import time

from pathlib import Path
import p4z3.util as util


# configure logging
log = logging.getLogger(__name__)

FILE_DIR = Path(__file__).parent.resolve()
# whitebox should be p4test, but this is quite slow right now...
WHITEBOX_BIN = FILE_DIR.joinpath("p4c/build/p4c")
BLACKBOX_BIN = FILE_DIR.joinpath("p4c/build/p4c")
TOFINO_BIN = FILE_DIR.joinpath("tofino/bf_src/install/bin/bf-p4c")
P4Z3_BIN = FILE_DIR.joinpath("p4c/build/p4toz3")
P4RANDOM_BIN = FILE_DIR.joinpath("p4c/build/p4bludgeon")

OUTPUT_DIR = FILE_DIR.joinpath("random")
GENERATOR_BUG_DIR = OUTPUT_DIR.joinpath("generator_bugs")
CRASH_BUG_DIR = OUTPUT_DIR.joinpath("crash_bugs")
VALIDATION_BUG_DIR = OUTPUT_DIR.joinpath("validation_bugs")
TIMEOUT_DIR = OUTPUT_DIR.joinpath("timeout_bugs")
ITERATIONS = 100
NUM_PROCESSES = 4

KNOWN_BUGS = [
    "Conditional execution",
    "Unimplemented compiler support",
    # bf
    "Unsupported on target",
    "PHV allocation was not successful",
    "Unsupported action spanning multiple stages",
    "shift count must be",
    "condition too complex",
    "condition expression too complex",
    "source of modify_field invalid",
    "Please consider simplifying",
    "Operands of arithmetic operations cannot be greater",
    "ListCompileTimeValue",
    "does not appear on the hash function",
    "Match group map doesn't match format size",
    "operating on container ",
    "Unable to find hi field slice associated with",
    "not yet handled by the ActionAnalysis pass",
    "invalid shift",
    "invalid slice on slice",
    "must be a PHV",
    "Cannot operate on values with different types",
    "operands have different types",
    "Fields involved in the same MAU operations have conflicting PARDE",
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


def generate_p4_dump(p4c_bin, p4_file, config):
    p4_cmd = f"{p4c_bin} "
    p4_cmd += f"{p4_file} "
    if config["use_tofino"]:
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
    try:
        p4_file.rename(target)
    except FileNotFoundError:
        log.warning("Could not move file %s, file not found!", p4_file)


def is_known_bug(result):
    for bug in KNOWN_BUGS:
        if bug in result.stderr.decode("utf-8"):
            log.info("Error \"%s\" already known. Skipping...", bug)
            return True
    return False


@timeout(seconds=600)
def validate_p4(p4_file, target_dir, p4c_bin, log_file):
    p4z3_cmd = "python3 check_p4_whitebox.py "
    p4z3_cmd += f"-i {p4_file} "
    p4z3_cmd += f"-o {target_dir} "
    p4z3_cmd += f"-p {p4c_bin} "
    p4z3_cmd += f"-l {log_file} "
    result = util.exec_process(p4z3_cmd)
    return result.returncode


@timeout(seconds=600)
def validate_p4_blackbox(p4_file, target_dir, log_file, config):
    p4z3_cmd = "python3 check_p4_blackbox.py "
    p4z3_cmd += f"-i {p4_file} "
    p4z3_cmd += f"-o {target_dir} "
    p4z3_cmd += f"-l {log_file} "
    if config["use_tofino"]:
        p4z3_cmd += f"-t "
    if config["randomize_input"]:
        p4z3_cmd += f"-r "
    result = util.exec_process(p4z3_cmd)
    time.sleep(3)
    return result.returncode


def validate(dump_dir, p4_file, log_file, config):
    try:
        # Tofino does not allow insights into the individual passes
        # So we are forced to use the blackbox technique
        if config["use_blackbox"]:
            result = validate_p4_blackbox(
                p4_file, dump_dir, log_file, config)
        else:
            result = validate_p4(p4_file, dump_dir, WHITEBOX_BIN, log_file)
    except TimeoutError:
        log.error("Validation timed out.")
        dump_file(TIMEOUT_DIR, p4_file)
        dump_file(TIMEOUT_DIR, log_file)
        # reset the dump directory
        return util.EXIT_FAILURE
    if result != util.EXIT_SUCCESS:
        log.error("Failed to validate the P4 code!")
        log.error("Rerun the example with:")
        out_file = VALIDATION_BUG_DIR.joinpath(p4_file.name)
        if config["use_tofino"]:
            err_log = dump_dir.joinpath(Path(p4_file.stem + "_ptf_err.log"))
            dump_file(VALIDATION_BUG_DIR, err_log)
        if config["use_blackbox"]:
            log.error("python3 check_p4_blackbox.py -i %s", out_file)
            stf_name = dump_dir.joinpath(Path(p4_file.stem + ".stf"))
            dump_file(VALIDATION_BUG_DIR, stf_name)
        else:
            log.error("python3 check_p4_whitebox.py -i %s", out_file)
        dump_file(VALIDATION_BUG_DIR, log_file)
        dump_file(VALIDATION_BUG_DIR, p4_file)
    return result


def check(idx, config):
    test_id = generate_id()
    test_name = f"{test_id}_{idx}"
    dump_dir = OUTPUT_DIR.joinpath(f"dmp_{test_name}")
    util.check_dir(dump_dir)
    log_file = dump_dir.joinpath(f"{test_name}.log")
    p4_file = dump_dir.joinpath(f"{test_name}.p4")
    log.info("Testing p4 program %s", p4_file)
    # generate a random program
    result, p4_file = generate_p4_dump(P4RANDOM_BIN, p4_file, config)
    if result.returncode != util.EXIT_SUCCESS:
        log.error("Failed generate P4 code!")
        dump_result(result, GENERATOR_BUG_DIR, p4_file)
        # reset the dump directory
        util.del_dir(dump_dir)
        return result.returncode
    # check compilation
    if config["use_tofino"]:
        result = compile_p4_prog(TOFINO_BIN, p4_file, dump_dir)
    elif config["use_blackbox"]:
        result = compile_p4_prog(BLACKBOX_BIN, p4_file, dump_dir)
    else:
        result = compile_p4_prog(WHITEBOX_BIN, p4_file, dump_dir)
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
    if config["do_validate"]:
        result = validate(dump_dir, p4_file, log_file, config)
    # reset the dump directory
    util.del_dir(dump_dir)
    return result


class TestLauncher():
    def __init__(self, config):
        self._config = config

    def __call__(self, idx):
        return check(idx, self._config)


def main(args):

    config = {}
    config["do_validate"] = args.do_validate
    config["use_tofino"] = args.use_tofino
    config["use_blackbox"] = args.use_blackbox
    config["randomize_input"] = args.randomize_input

    # configure logging
    logging.basicConfig(filename=args.log_file,
                        format="%(levelname)s:%(message)s",
                        level=logging.INFO,
                        filemode='w')
    stderr_log = logging.StreamHandler()
    stderr_log.setFormatter(logging.Formatter("%(levelname)s:%(message)s"))
    log.addHandler(stderr_log)

    util.check_dir(OUTPUT_DIR)

    # initialize with some pre-configured state
    launch = TestLauncher(config)

    if config["use_tofino"] and config["do_validate"]:
        config["use_blackbox"] = True
        # tofino only supports single threaded mode for now
        for idx in range(args.iterations):
            launch(idx)
        return
    # this sometimes deadlocks, no idea why....
    with Pool(args.num_processes) as p:
        p.map(launch, range(args.iterations))
    return


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--use-blackbox", "-b", dest="use_blackbox",
                        action='store_true',
                        help="Use the blackbox technique instead of"
                        "translation validation.")
    parser.add_argument("--use-tofino", "-t", dest="use_tofino",
                        action='store_true',
                        help="Use the Tofino backend instead of BMV2.")
    parser.add_argument("-l", "--log_file", dest="log_file",
                        default="random.log",
                        help="Specifies name of the log file.")
    parser.add_argument("-v", "--validate", dest="do_validate",
                        action='store_true',
                        help="Also perform validation on programs.")
    parser.add_argument("-i", "--iterations", dest="iterations",
                        default=ITERATIONS, type=int,
                        help="How many iterations to run.")
    parser.add_argument("-p", "--num_processes", dest="num_processes",
                        default=NUM_PROCESSES, type=int,
                        help="How many processes to launch.")
    parser.add_argument("-o", "--out_dir", dest="out_dir",
                        default=OUTPUT_DIR,
                        help="The output folder where all tests are dumped.")
    parser.add_argument("-r", "--randomize-input", dest="randomize_input",
                        action='store_true',
                        help="Whether to randomize the z3 input variables.")
    # Parse options and process argv
    args = parser.parse_args()
    main(args)




# class TestLauncher(multiprocessing.Process):

#     def __init__(self, config, idx_range):
#         multiprocessing.Process.__init__(self)
#         self.name = "TestLauncher"
#         self._config = config
#         self.kill = multiprocessing.Event()
#         self.idx_range = idx_range

#     def run(self):
#         for idx in self.idx_range:
#             check(idx, self._config)

#     def terminate(self):
#         log.info("%s: Received termination signal! Exiting..", self.name)
#         self.kill.set()

#     def baskets_from(items, bucket_size):
#         baskets = [[] for _ in range(bucket_size)]
#         for i, item in enumerate(items):
#             baskets[i % bucket_size].append(item)
#         return filter(None, baskets)
#     distributions = baskets_from(range(args.iterations), NUM_PROCESSES)
#     procs = []
#     for dis in distributions:
#         proc = TestLauncher(config, dis)
#         procs.append(proc)
#         proc.start()

#     for p in procs:
#         p.join()
