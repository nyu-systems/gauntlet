import argparse
from pathlib import Path
import os
import imp
import logging
from p4z3.base import Z3Reg, z3
import p4z3.util as util

log = logging.getLogger(__name__)
FILE_DIR = os.path.dirname(os.path.abspath(__file__))


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
    failed = [f"{p4_file}.py", f"{p4_file}.p4"]
    util.copy_file(failed, fail_dir)


def get_z3_repr(p4_module, p4_path, fail_dir):
    try:
        z3_reg, v1model = p4_module(Z3Reg())
        p4_ctrl = v1model.ig
        z3_reg.register_inouts("inouts", p4_ctrl.args)
        p4_vars = z3_reg.instance("", z3_reg.type("inouts"))
        p4_vars.add_externs(z3_reg._externs)
        z3_ast = p4_ctrl.eval(p4_vars, [])
    except Exception:
        log.exception("Failed to compile Python to Z3:\n")
        if fail_dir:
            handle_pyz3_error(fail_dir, p4_path)
            debug_msg([p4_path, p4_path])
        return None
    return z3_ast


def check_equivalence(prog_before, prog_after):
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same
    ''' SOLVER '''
    s = z3.Solver()
    # the equivalence equation
    tv_equiv = z3.simplify(prog_before) != z3.simplify(prog_after)
    s.add(tv_equiv)
    log.debug(s.sexpr())
    ret = s.check()
    log.debug(tv_equiv)
    log.debug(ret)
    if ret == z3.sat:
        log.error("PROGRAM BEFORE\n%s", prog_before)
        log.error("PROGRAM AFTER\n%s", prog_after)
        log.error(s.model())
        log.error("Detected an equivalence violation!")
        return util.EXIT_VIOLATION
    else:
        return util.EXIT_SUCCESS


def get_ctrl_module(prog_path):
    ctrl_dir = prog_path.parent
    ctrl_name = prog_path.stem
    ctrl_function = "p4_program"
    try:
        ctrl_module = import_prog(ctrl_dir, ctrl_name, ctrl_function)
    except ImportError as e:
        log.error(("Could not import the"
                   "requested control function: %s", e))
        return None
    return ctrl_module


def z3_check(prog_paths, fail_dir=None):
    if len(prog_paths) < 2:
        log.error("The equivalence check requires at least two input programs!")
        return util.EXIT_FAILURE
    for i in range(1, len(prog_paths)):
        # We do not support the flatten passes right now
        # Reason is they generate entirely new variables
        # which cause z3 to generate a false positive
        if "Flatten" in prog_paths[i - 1] or "Flatten" in prog_paths[i]:
            log.warning("Skipping \"Flatten\" passes because of z3 crash...")
            continue
        p4_pre_path = Path(prog_paths[i - 1])
        p4_post_path = Path(prog_paths[i])

        p4_pre = get_ctrl_module(p4_pre_path)
        p4_post = get_ctrl_module(p4_post_path)
        if p4_pre is None or p4_post is None:
            return util.EXIT_FAILURE
        log.info("Comparing programs\n%s\n%s\n########",
                 p4_pre_path.stem, p4_post_path.stem)
        ctrl_fun_pre = get_z3_repr(p4_pre, p4_pre_path, fail_dir)
        ctrl_fun_post = get_z3_repr(p4_post, p4_post_path, fail_dir)
        if ctrl_fun_pre is None or ctrl_fun_post is None:
            return util.EXIT_FAILURE
        ret = check_equivalence(ctrl_fun_pre, ctrl_fun_post)
        if ret != util.EXIT_SUCCESS:
            if fail_dir:
                handle_pyz3_error(fail_dir, p4_pre_path)
                handle_pyz3_error(fail_dir, p4_post_path)
                debug_msg([p4_pre_path, p4_post_path])
            return ret
    return util.EXIT_SUCCESS


def main(args=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--progs", "-p", dest="progs",
                        type=str, nargs='+', required=True,
                        help="The ordered list of programs to compare.")
    args = parser.parse_args(args)
    return z3_check(args.progs)


if __name__ == '__main__':
    main()
