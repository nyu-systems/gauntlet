import z3
from p4z3_base import *
import os
import argparse
from pathlib import Path

FILE_DIR = os.path.dirname(os.path.abspath(__file__))


def import_prog(module, prog_name):
    """ Try to import a module and class directly instead of the typical
        Python method. Allows for dynamic imports. """
    print(module)
    print(prog_name)
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

    print("PROGRAM 1")
    print(p4_ctrl_0(p4_ctrl_0_args))
    print("PROGRAM 2")
    print(p4_ctrl_1(p4_ctrl_1_args))
    # the equivalence equation
    tv_equiv = z3.simplify(p4_ctrl_0(p4_ctrl_0_args) !=
                           p4_ctrl_1(p4_ctrl_1_args))
    s.add(tv_equiv)
    print(tv_equiv)
    print (s.sexpr())
    ret = s.check()
    if ret == z3.sat:
        print (ret)
        print (s.model())
        return os.EX_PROTOCOL
    else:
        print (ret)
        return os.EX_OK


def z3_check(args=None):
    p = argparse.ArgumentParser()
    p.add_argument("--progs", "-p", dest="progs",
                   type=str, nargs='+', required=True,
                   help="The ordered list of programs to compare.")
    args = p.parse_args(args)
    if len(args.progs) < 2:
        print("""ERROR: The equivalence check requires at least two input programs!""", file=sys.stderr)
        p.print_help()
        exit(1)

    ctrls = []
    for path in args.progs:
        prog_path = Path(path)
        ctrl_name = prog_path.parent.joinpath(prog_path.stem)
        ctrl_function = "p4_program"
        try:
            ctrl_module = import_prog(str(ctrl_name).replace('/', '.'), ctrl_function)
            ctrls.append(ctrl_module)
        except ImportError as e:
            print("Could not import the requested control function: %s " %
                  e, file=sys.stderr)
            exit(1)

    for index, ctrl_fun in enumerate(ctrls):
        if index < len(ctrls) - 1:
            check_equivalence(ctrls[index], ctrls[index + 1])


if __name__ == '__main__':
    z3_check()
