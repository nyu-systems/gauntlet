import argparse
import logging as log
from pathlib import Path
import sys
import imp

import z3
import p4pyz3.util as util
from p4pyz3.p4z3_base import *

FILE_DIR = os.path.dirname(os.path.abspath(__file__))
# avoid annoying import errors...
sys.path.append(FILE_DIR)


def import_prog(ctrl_dir, ctrl_name, prog_name):
    """ Try to import a module and class directly instead of the typical
        Python method. Allows for dynamic imports. """
    mod_info = imp.find_module(ctrl_name, [ctrl_dir])
    module = imp.load_module("tmp_module", *mod_info)
    return getattr(module, prog_name)


def check_equivalence(p4_program_0, p4_program_1):
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same
    ''' SOLVER '''
    s = z3.Solver()
    try:
        p4_ctrl_0, p4_ctrl_0_args = p4_program_0(Z3Reg())[2]
        p4_ctrl_1, p4_ctrl_1_args = p4_program_1(Z3Reg())[2]
        prog_before = p4_ctrl_0(p4_ctrl_0_args)
        prog_after = p4_ctrl_1(p4_ctrl_1_args)
        log.debug("PROGRAM BEFORE", prog_before)
        log.debug("PROGRAM AFTER", prog_after)
    except Exception as e:
        log.exception("Failed to translate Python to Z3:\n")
        return util.EXIT_FAILURE
    # the equivalence equation
    tv_equiv = z3.simplify(prog_before != prog_after)
    s.add(tv_equiv)
    log.info(tv_equiv)
    log.info(s.sexpr())
    ret = s.check()
    if ret == z3.sat:
        log.info(ret)
        log.info(s.model())
        return util.EXIT_FAILURE
    else:
        log.info(ret)
        return util.EXIT_SUCCESS


def z3_check(prog_paths, fail_dir=f"./failed/"):
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
            ctrl_module = import_prog(
                ctrl_dir, ctrl_name, ctrl_function)
            ctrls.append((path, ctrl_module))
        except ImportError as e:
            log.error(("Could not import the"
                       "requested control function: %s" % e))
            return util.EXIT_FAILURE
    for i, _ in enumerate(ctrls):
        if i < len(ctrls) - 1:
            ctrl_fun_pre = ctrls[i][1]
            ctrl_fun_post = ctrls[i + 1][1]
            ret = check_equivalence(ctrl_fun_pre, ctrl_fun_post)
            if ret != util.EXIT_SUCCESS:
                util.check_dir(fail_dir)
                failed = [ctrls[i][0] + ".py", ctrls[i + 1][0] + ".py",
                          ctrls[i][0] + ".p4", ctrls[i + 1][0] + ".p4"]
                util.copy_file(failed, fail_dir)
                return ret
    return util.EXIT_SUCCESS


def main(args=None):
    p = argparse.ArgumentParser()
    p.add_argument("--progs", "-p", dest="progs",
                   type=str, nargs='+', required=True,
                   help="The ordered list of programs to compare.")
    args = p.parse_args(args)
    if len(args.progs) < 2:
        log.error("ERROR: The equivalence check " +
                  "requires at least two input programs!")
        p.print_help()
        return util.EXIT_FAILURE
    return z3_check(arg.progs)


if __name__ == '__main__':
    z3_check()
