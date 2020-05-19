import argparse
from pathlib import Path
import os
import sys
import importlib
import logging
from p4z3 import Z3Reg, P4Package, z3
import p4z3.util as util
sys.setrecursionlimit(15000)


FILE_DIR = os.path.dirname(os.path.abspath(__file__))
log = logging.getLogger(__name__)


# We maintain a list of passes that causes segmentation faults
# TODO: Fix these, likely by using simulation relations
SKIPPED_PASSES = [
    "FlattenHeaders",
    "FlattenInterfaceStructs",
    # "InlineActions",
    # "InlineFunctions",
    # "UniqueNames",
    # "UniqueParameters",
    # "SpecializeAll",
    "ExpandLookahead",
    "RenameUserMetadata",
]


def needs_skipping(post):
    for skip_pass in SKIPPED_PASSES:
        if skip_pass in post:
            log.warning("Skipping \"%s\" pass to avoid crashes...", skip_pass)
            return True
    return False


def import_prog(ctrl_dir, ctrl_name, prog_name):
    """ Try to import a module and class directly instead of the typical
        Python method. Allows for dynamic imports. """
    finder = importlib.machinery.PathFinder()
    # unfortunately this does not support Posix paths and silently fails
    # this is a standard lib function...
    module_specs = finder.find_spec(str(ctrl_name), [str(ctrl_dir)])
    module = module_specs.loader.load_module()
    return getattr(module, prog_name)


def debug_msg(p4_files):
    debug_string = "You can debug this failure by running:\n"
    debug_string += f"python3 {FILE_DIR}/{Path(__file__).stem}.py --progs "
    for p4_file in p4_files:
        p4_file_name = p4_file.stem
        p4_file_dir = p4_file.parent
        debug_string += f" {p4_file_dir}/failed/{p4_file_name} "
    log.error(debug_string)


def handle_pyz3_error(fail_dir, p4_file):
    util.check_dir(fail_dir)
    failed = [p4_file.with_suffix(".py"), p4_file.with_suffix(".p4i")]
    util.copy_file(failed, fail_dir)


def evaluate_package(p4_package):
    z3_asts = {}
    # only P4Package instances are valid inputs
    if not isinstance(p4_package, P4Package):
        return z3_asts

    for pipe_name, p4_pipe_ast in p4_package.pipes.items():
        # if pipe_name != "ig":
        #     continue
        if isinstance(p4_pipe_ast, P4Package):
            # it is apparently possible to have nested packages...
            z3_tmp_asts = evaluate_package(p4_pipe_ast)
            for key, val in z3_tmp_asts.items():
                name = f"{p4_pipe_ast.name}_{key}"
                z3_asts[name] = val
        else:
            z3_asts[pipe_name] = p4_pipe_ast
        # all other types are nonsense and we should not bother with them
        # else:
            # raise RuntimeError(
            # f"Unexpected Input Pipe {p4_pipe_ast} Type: {type(p4_pipe_ast)} !")
    return z3_asts


def get_z3_asts(p4_module, p4_path, fail_dir):

    log.info("Loading %s ASTs...", p4_path.name)
    z3_asts = {}
    try:
        package = p4_module(Z3Reg())
        if not package:
            log.warning("No main module, nothing to evaluate!")
            return z3_asts, util.EXIT_SKIPPED
        z3_asts = evaluate_package(package)
    except Exception:
        log.exception("Failed to compile Python to Z3:\n")
        if fail_dir:
            handle_pyz3_error(fail_dir, p4_path)
            debug_msg([p4_path, p4_path])
        return z3_asts, util.EXIT_FAILURE
    return z3_asts, util.EXIT_SUCCESS


def check_equivalence(prog_before, prog_after):
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same
    ''' SOLVER '''
    # s = z3.Solver()
    try:
        # the equivalence equation
        log.debug("Simplifying equation...")
        tv_equiv = z3.simplify(prog_before != prog_after)
    except z3.Z3Exception as e:
        prog_before_simpl = z3.simplify(prog_before)
        prog_after_simpl = z3.simplify(prog_after)
        log.error("Failed to compare z3 formulas!\nReason: %s", e)
        log.error("PROGRAM BEFORE\n%s", prog_before_simpl)
        log.error("PROGRAM AFTER\n%s", prog_after_simpl)
        return util.EXIT_VIOLATION
    log.debug("Checking...")
    g = z3.Goal()
    log.debug(z3.tactics())
    g.add(tv_equiv)
    t = z3.Then(
        z3.Tactic("qflia"),
        z3.Tactic("propagate-values"),
        z3.Tactic("ctx-solver-simplify"),
        z3.Tactic("elim-and")
    )
    s = t.solver()
    log.debug(s.sexpr())
    ret = s.check(tv_equiv)
    log.debug(tv_equiv)
    log.debug(ret)
    if ret == z3.sat:
        prog_before_simpl = z3.simplify(prog_before)
        prog_after_simpl = z3.simplify(prog_after)
        log.error("Detected an equivalence violation!")
        log.error("PROGRAM BEFORE\n%s", prog_before_simpl)
        log.error("PROGRAM AFTER\n%s", prog_after_simpl)
        log.error("Proposed solution:")
        log.error(s.model())
        return util.EXIT_VIOLATION
    else:
        return util.EXIT_SUCCESS


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


def get_z3_formulization(p4_pre_path, fail_dir):
    p4_pre = get_py_module(p4_pre_path)
    if p4_pre is None:
        return None, util.EXIT_FAILURE
    pipes_pre, result = get_z3_asts(p4_pre, p4_pre_path, fail_dir)
    if result != util.EXIT_SUCCESS:
        return None, result

    return pipes_pre, result


def z3_check(prog_paths, fail_dir=None):
    if len(prog_paths) < 2:
        log.error("Equivalence checks require at least two input programs!")
        return util.EXIT_FAILURE
    z3_progs = []
    for p4_prog in prog_paths:
        p4_path = Path(p4_prog)
        pipes, result = get_z3_formulization(p4_path, fail_dir)
        if result != util.EXIT_SUCCESS:
            return result
        z3_progs.append((p4_path, pipes))
    for idx in range(1, len(z3_progs)):

        p4_pre_path, pipes_pre = z3_progs[idx - 1]
        p4_post_path, pipes_post = z3_progs[idx]
        log.info("\nComparing programs\n%s\n%s\n########",
                 p4_pre_path.stem, p4_post_path.stem)
        # We do not support the passes which rename variables right now
        # Reason is they generate entirely new variables
        # which cause z3 to crash for some reason...
        if needs_skipping(str(p4_post_path)):
            continue
        if len(pipes_pre) != len(pipes_post):
            log.warning("Pre and post model differ in size!")
            return util.EXIT_SKIPPED
        for pipe_name in pipes_pre:
            pipe_pre = pipes_pre[pipe_name]
            pipe_post = pipes_post[pipe_name]
            log.info("Checking z3 equivalence for pipe %s...", pipe_name)
            ret = check_equivalence(pipe_pre, pipe_post)
            if ret != util.EXIT_SUCCESS:
                if fail_dir:
                    handle_pyz3_error(fail_dir, p4_pre_path)
                    handle_pyz3_error(fail_dir, p4_post_path)
                    debug_msg([p4_pre_path, p4_post_path])
                return ret
    log.info("Passed all checks!")
    return util.EXIT_SUCCESS


def main(args=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--progs", "-p", dest="progs",
                        type=str, nargs='+', required=True,
                        help="The ordered list of programs to compare.")
    args = parser.parse_args(args)
    return z3_check(args.progs)


if __name__ == '__main__':
    # configure logging
    logging.basicConfig(filename="analysis.log",
                        format="%(levelname)s:%(message)s",
                        level=logging.INFO,
                        filemode='w')
    stderr_log = logging.StreamHandler()
    stderr_log.setFormatter(logging.Formatter("%(levelname)s:%(message)s"))
    logging.getLogger().addHandler(stderr_log)
    main()
