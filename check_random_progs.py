import random
import string
import logging
from pathlib import Path
import p4z3.util as util

# configure logging
log = logging.getLogger(__name__)

FILE_DIR = Path(__file__).parent.resolve()
P4C_BIN = FILE_DIR.joinpath("p4c/build/p4c-bm2-ss")
P4Z3_BIN = FILE_DIR.joinpath("p4c/build/p4toz3")
P4RANDOM_BIN = FILE_DIR.joinpath("p4c/build/p4bludgeon")

OUTPUT_DIR = FILE_DIR.joinpath("random")
GENERATOR_BUG_DIR = OUTPUT_DIR.joinpath("generator_bugs")
CRASH_BUG_DIR = OUTPUT_DIR.joinpath("crash_bugs")
VALIDATION_BUG_DIR = OUTPUT_DIR.joinpath("validation_bugs")


KNOWN_BUGS = [
    "could not evaluate at compilation time",
    "Conditional execution in actions is not supported on this target",
    "Number of errors exceeded set maximum of",
    "Too many heap sections",
    "Unsupported MethodCallStatement not yet supported on this target",
]


def generate_id():
    sw_id = "".join(random.choice("".join([random.choice(
        string.ascii_letters + string.digits)
        for ch in range(4)])) for _ in range(4))
    return sw_id


def generate_p4_dump(p4c_bin, p4_file):
    p4_cmd = f"{p4c_bin} "
    p4_cmd += f"{p4_file} "
    log.debug("Generating random p4 code with command %s ", p4_cmd)
    return util.exec_process(p4_cmd), p4_file


def compile_p4_prog(p4c_bin, p4_file):
    p4_cmd = f"{p4c_bin} "
    # p4_cmd += f"-vvvv "
    p4_cmd += f"{p4_file} "
    log.debug("Checking compilation with command %s ", p4_cmd)
    return util.exec_process(p4_cmd)


def dump_result(result, target_dir, p4_file):
    util.check_dir(target_dir)
    test_id = target_dir.joinpath(p4_file.stem)
    with open(f"{test_id}.err", 'w+') as err_file:
        err_file.write(result.stderr.decode("utf-8"))


def dump_p4_file(target_dir, p4_file):
    target = target_dir.joinpath(p4_file.name)
    p4_file.rename(target)


def is_known_bug(result):
    for bug in KNOWN_BUGS:
        if bug in result.stderr.decode("utf-8"):
            log.info("Error \"%s\" already known. Skipping...", bug)
            return True
    return False


def main():
    util.check_dir(OUTPUT_DIR)
    test_id = generate_id()
    for idx in range(500):
        test_name = f"{test_id}_{idx}"
        p4_file = OUTPUT_DIR.joinpath(f"{test_name}.p4")

        result, p4_file = generate_p4_dump(P4RANDOM_BIN, p4_file)
        if result.returncode != util.EXIT_SUCCESS:
            log.info("Failed generate P4 code!")
            dump_result(result, GENERATOR_BUG_DIR, p4_file)
            continue

        result = compile_p4_prog(P4C_BIN, p4_file)
        if result.returncode != util.EXIT_SUCCESS:
            if not is_known_bug(result):
                log.info("Failed to compile the P4 code!")
                log.info("Found a new bug!")
                dump_result(result, CRASH_BUG_DIR, p4_file)
                dump_p4_file(CRASH_BUG_DIR, p4_file)
                continue
        p4_file.unlink()
    return util.EXIT_SUCCESS


if __name__ == '__main__':
    # configure logging
    logging.basicConfig(filename="random.log",
                        format="%(levelname)s:%(message)s",
                        level=logging.INFO,
                        filemode='w')
    stderr_log = logging.StreamHandler()
    stderr_log.setFormatter(logging.Formatter("%(levelname)s:%(message)s"))
    log.addHandler(stderr_log)
    main()
