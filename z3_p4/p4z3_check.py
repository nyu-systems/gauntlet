import argparse
import logging as log
from pathlib import Path
import util

import z3
from p4z3_base import *

FILE_DIR = os.path.dirname(os.path.abspath(__file__))


def import_prog(module, prog_name):
    """ Try to import a module and class directly instead of the typical
        Python method. Allows for dynamic imports. """
    module = __import__(module, fromlist=[prog_name])
    return getattr(module, prog_name)


def check_equivalence(p4_program_0, p4_program_1):
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same
    ''' SOLVER '''
    s = z3.Solver()
    p4_ctrl_0, p4_ctrl_0_args = p4_program_0(Z3Reg())[2]
    p4_ctrl_1, p4_ctrl_1_args = p4_program_1(Z3Reg())[2]

    log.debug("PROGRAM 1")
    log.debug(p4_ctrl_0(p4_ctrl_0_args))
    log.debug("PROGRAM 2")
    log.debug(p4_ctrl_1(p4_ctrl_1_args))
    # the equivalence equation
    tv_equiv = z3.simplify(p4_ctrl_0(p4_ctrl_0_args) !=
                           p4_ctrl_1(p4_ctrl_1_args))
    s.add(tv_equiv)
    log.info(tv_equiv)
    log.info(s.sexpr())
    ret = s.check()
    if ret == z3.sat:
        log.info(ret)
        log.info(s.model())
        return util.EXIT_SUCCESS
    else:
        log.error(ret)
        return util.EXIT_FAILURE


def z3_check(args=None):
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

    ctrls = []
    for path in args.progs:
        prog_path = Path(path)
        ctrl_name = prog_path.parent.joinpath(prog_path.stem)
        ctrl_function = "p4_program"
        try:
            ctrl_module = import_prog(
                str(ctrl_name).replace('/', '.'), ctrl_function)
            ctrls.append(ctrl_module)
        except ImportError as e:
            log.error(("Could not import the"
                       "requested control function: %s" % e))
            return util.EXIT_FAILURE

    for index, ctrl_fun in enumerate(ctrls):
        if index < len(ctrls) - 1:
            ret = check_equivalence(ctrls[index], ctrls[index + 1])
            if ret != util.EXIT_SUCCESS:
                return ret


if __name__ == '__main__':
    z3_check()
