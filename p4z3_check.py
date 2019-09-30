import argparse
from pathlib import Path
import sys
import imp
import logging as log

import z3
import p4z3.util as util
from p4z3.base import *

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


def get_z3_repr(p4_ctrl, fail_dir):
    p4_file = p4_ctrl[0]
    p4_program = p4_ctrl[1]
    try:
        p4_ctrl, p4_ctrl_args = p4_program(Z3Reg())[2]
        z3_ast = p4_ctrl(p4_ctrl_args)
    except Exception as e:
        log.exception("Failed to compile Python to Z3:\n")
        if fail_dir:
            handle_pyz3_error(fail_dir, p4_file)
            debug_msg([p4_file])
        return None
    return z3_ast


def check_equivalence(prog_before, prog_after):
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same
    ''' SOLVER '''
    s = z3.Solver()
    log.debug("PROGRAM BEFORE\n%s" % prog_before)
    log.debug("PROGRAM AFTER\n%s" % prog_after)
    # the equivalence equation
    tv_equiv = z3.simplify(prog_before != prog_after)
    s.add(tv_equiv)
    log.debug(tv_equiv)
    log.debug(s.sexpr())
    ret = s.check()
    if ret == z3.sat:
        log.error(ret)
        log.error(s.model())
        log.error("Detected an equivalence violation!")
        return util.EXIT_FAILURE
    else:
        log.debug(ret)
        return util.EXIT_SUCCESS


def z3_check(prog_paths, fail_dir=None):
    if len(prog_paths) < 2:
        log.error("The equivalence check " +
                  "requires at least two input programs!")
        return util.EXIT_FAILURE
    ctrls = []
    for path in prog_paths:
        prog_path = Path(path)
        ctrl_dir = prog_path.parent
        ctrl_name = prog_path.stem
        ctrl_function = "p4_program"
        try:
            ctrl_module = import_prog(ctrl_dir, ctrl_name, ctrl_function)
            ctrls.append((prog_path, ctrl_module))
        except ImportError as e:
            log.error(("Could not import the"
                       "requested control function: %s" % e))
            return util.EXIT_FAILURE
    for i, _ in enumerate(ctrls):
        if i < len(ctrls) - 1:
            ctrl_fun_pre = get_z3_repr(ctrls[i], fail_dir)
            ctrl_fun_post = get_z3_repr(ctrls[i + 1], fail_dir)
            if ctrl_fun_pre is None or ctrl_fun_post is None:
                return util.EXIT_FAILURE
            ret = check_equivalence(ctrl_fun_pre, ctrl_fun_post)
            if ret != util.EXIT_SUCCESS:
                if fail_dir:
                    p4_file_pre = ctrls[i][0]
                    p4_file_post = ctrls[i + 1][0]
                    handle_pyz3_error(fail_dir, p4_file_pre)
                    handle_pyz3_error(fail_dir, p4_file_post)
                    debug_msg([p4_file_pre, p4_file_post])
                return ret
    return util.EXIT_SUCCESS


def main(args=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--progs", "-p", dest="progs",
                        type=str, nargs='+', required=True,
                        help="The ordered list of programs to compare.")
    args = parser.parse_args(args)
    if len(args.progs) < 2:
        log.error("ERROR: The equivalence check " +
                  "requires at least two input programs!")
        p.print_help()
        return util.EXIT_FAILURE
    return z3_check(args.progs)


if __name__ == '__main__':
    main()
