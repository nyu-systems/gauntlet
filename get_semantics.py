import argparse
from pathlib import Path
import sys
import importlib
import logging
from p4z3 import Z3Reg
import p4z3.util as util
sys.setrecursionlimit(15000)


FILE_DIR = Path(__file__).parent.resolve()
P4Z3_BIN = FILE_DIR.joinpath("p4c/build/p4toz3")
log = logging.getLogger(__name__)


def import_prog(ctrl_dir, ctrl_name, prog_name):
    """ Try to import a module and class directly instead of the typical
        Python method. Allows for dynamic imports. """
    finder = importlib.machinery.PathFinder()
    # unfortunately this does not support Posix paths and silently fails
    # this is a standard lib function...
    module_specs = finder.find_spec(str(ctrl_name), [str(ctrl_dir)])
    module = module_specs.loader.load_module()
    return getattr(module, prog_name)


def get_z3_asts(p4_module, p4_path):

    log.info("Loading %s ASTs...", p4_path.name)
    z3_asts = {}
    try:
        p4_package = p4_module(Z3Reg())
        if not p4_package:
            log.warning("No main module, nothing to evaluate!")
            return z3_asts, util.EXIT_SKIPPED
        z3_asts = p4_package.get_pipes()
    except Exception:
        log.exception("Failed to compile Python to Z3:\n")
        return z3_asts, util.EXIT_FAILURE
    return z3_asts, util.EXIT_SUCCESS


def get_py_module(prog_path):
    ctrl_dir = prog_path.parent
    ctrl_name = prog_path.stem
    ctrl_function = "p4_program"
    try:
        ctrl_module = import_prog(ctrl_dir, ctrl_name, ctrl_function)
    except (ImportError, SyntaxError) as e:
        log.error(("Could not import the "
                   "requested module: %s", e))
        return None
    return ctrl_module


def run_p4_to_py(p4_file, py_file):
    cmd = f"{P4Z3_BIN} "
    cmd += f"{p4_file} "
    cmd += f"--output {py_file} "
    return util.exec_process(cmd)


def get_z3_formulization(p4_file):

    if p4_file.suffix == ".p4":
        py_file = FILE_DIR.joinpath(p4_file.with_suffix(".py").name)
        result = run_p4_to_py(p4_file, py_file)
        p4_file = py_file
        if result.returncode != util.EXIT_SUCCESS:
            log.error("Failed to translate P4 to Python.")
            log.error("Compiler crashed!")
            return None, result.returncode

    p4py_module = get_py_module(p4_file)
    if p4py_module is None:
        return None, util.EXIT_FAILURE
    pipes_pre, result = get_z3_asts(p4py_module, p4_file)
    if result != util.EXIT_SUCCESS:
        return None, result
    return pipes_pre, result


def main(args=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--p4_input", dest="p4_input", default=None,
                        type=lambda x: util.is_valid_file(parser, x),
                        help="The main input p4 file. This can either be a P4"
                        " program or the Python ToZ3 IR.")
    args = parser.parse_args(args)
    p4_prog, result = get_z3_formulization(args.p4_input)
    if result != util.EXIT_FAILURE:
        for pipe_name, pipe_val in p4_prog.items():
            log.info("-" * 20)
            log.info("PIPE %s", pipe_name)
            log.info(pipe_val)
    return result


if __name__ == '__main__':
    # configure logging
    logging.basicConfig(filename="semantics.log",
                        format="%(levelname)s:%(message)s",
                        level=logging.INFO,
                        filemode='w')
    stderr_log = logging.StreamHandler()
    stderr_log.setFormatter(logging.Formatter("%(levelname)s:%(message)s"))
    logging.getLogger().addHandler(stderr_log)
    main()
