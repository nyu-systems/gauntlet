import argparse
from pathlib import Path
import os
import imp
import logging
from p4z3.base import Z3Reg, P4Package, z3
import p4z3.util as util

FILE_DIR = os.path.dirname(os.path.abspath(__file__))
log = logging.getLogger(__name__)


# We maintain a list of passes that causes segmentation faults
# TODO: Fix these, likely by using simulation relations
SKIPPED_PASSES = ["FlattenHeaders", "FlattenInterfaceStructs", "NestedStructs",
                  "UniqueNames", "RemoveActionParameters", "UniqueParameters",
                  "Inline", "SpecializeAll"]


def needs_skipping(pre, post):
    for skip_pass in SKIPPED_PASSES:
        if skip_pass in post:
            log.warning("Skipping \"%s\" pass to avoid crashes...", skip_pass)
            return True
    return False


def import_prog(ctrl_dir, ctrl_name, prog_name):
    """ Try to import a module and class directly instead of the typical
        Python method. Allows for dynamic imports. """
    mod_info = imp.find_module(ctrl_name, [ctrl_dir])
    module = imp.load_module("tmp_module", *mod_info)
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
    failed = [f"{p4_file}.py", f"{p4_file}.p4i"]
    util.copy_file(failed, fail_dir)


def evaluate_package(p4_package):
    z3_asts = {}
    for pipe_name, p4_pipe_ast in p4_package.pipes.items():

        # ignore deparser and emit because externs are hard...
        if pipe_name == "dep":
            continue
        log.info("Evaluating %s Python pipe...", pipe_name)
        if isinstance(p4_pipe_ast, P4Package):
            # it is apparently possible to have nested packages...
            z3_tmp_asts = evaluate_package(p4_pipe_ast)
            for key, val in z3_tmp_asts.items():
                name = f"{p4_pipe_ast.name}_{key}"
                z3_asts[name] = val
        elif p4_pipe_ast:
            z3_asts[pipe_name] = p4_pipe_ast.eval()
    return z3_asts


def get_z3_asts(p4_module, p4_path, fail_dir):
    z3.reset_params()
    log.info("Loading %s ASTs...", p4_path.name)
    z3_asts = {}
    try:
        package = p4_module(Z3Reg())
        if not package:
            log.warning("No main module, nothing to evaluate!")
            return z3_asts
        z3_asts = evaluate_package(package)
    except Exception:
        log.exception("Failed to compile Python to Z3:\n")
        if fail_dir:
            handle_pyz3_error(fail_dir, p4_path)
            debug_msg([p4_path, p4_path])
        return util.EXIT_FAILURE
    return z3_asts


def check_equivalence(prog_before, prog_after):
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same
    ''' SOLVER '''
    log.info("Checking z3 formula...")
    s = z3.Solver()
    # the equivalence equation
    prog_before_simpl = z3.simplify(prog_before)
    prog_after_simpl = z3.simplify(prog_after)
    tv_equiv = prog_before_simpl != prog_after_simpl
    # tv_equiv = z3.Not(z3.eq(prog_before_simpl, prog_after_simpl))
    s.add(tv_equiv)
    log.debug(s.sexpr())
    ret = s.check()
    log.debug(tv_equiv)
    log.debug(ret)
    if ret == z3.sat:
        log.error("PROGRAM BEFORE\n%s", prog_before_simpl)
        log.error("PROGRAM AFTER\n%s", prog_after_simpl)
        log.error("Proposed solution:")
        log.error(s.model())
        log.error("Detected an equivalence violation!")
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


def z3_check(prog_paths, fail_dir=None):
    if len(prog_paths) < 2:
        log.error("Equivalence checks require at least two input programs!")
        return util.EXIT_FAILURE
    for i in range(1, len(prog_paths)):
        # We do not support the passes which rename variables right now
        # Reason is they generate entirely new variables
        # which cause z3 to crash for some reason...
        if needs_skipping(prog_paths[i - 1], prog_paths[i]):
            continue
        p4_pre_path = Path(prog_paths[i - 1])
        p4_post_path = Path(prog_paths[i])

        p4_pre = get_py_module(p4_pre_path)
        p4_post = get_py_module(p4_post_path)
        if p4_pre is None or p4_post is None:
            return util.EXIT_FAILURE
        log.info("\nComparing programs\n%s\n%s\n########",
                 p4_pre_path.stem, p4_post_path.stem)
        pipes_pre = get_z3_asts(p4_pre, p4_pre_path, fail_dir)
        pipes_post = get_z3_asts(p4_post, p4_post_path, fail_dir)
        if pipes_pre == util.EXIT_FAILURE or pipes_post == util.EXIT_FAILURE:
            return util.EXIT_FAILURE
        if not pipes_pre or not pipes_post:
            log.error("Pipes did not generate any AST!")
            return util.EXIT_SKIPPED
        if len(pipes_pre) != len(pipes_post):
            log.error("Pre and post model differ in size!")
            return util.EXIT_FAILURE
        for pipe_name in pipes_pre:
            pipe_pre = pipes_pre[pipe_name]
            pipe_post = pipes_post[pipe_name]
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
