import argparse
from pathlib import Path
import sys
import importlib
import logging

from p4z3.contrib.tabulate import tabulate
from p4z3 import z3, Z3Reg, P4ComplexType, P4Extern

import p4z3.util as util
from p4z3.core import core_externs


sys.setrecursionlimit(15000)


FILE_DIR = Path(__file__).parent.resolve()
P4Z3_BIN = FILE_DIR.joinpath("modules/p4c/build/p4toz3")
OUT_DIR = FILE_DIR.joinpath("validated")
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
        z3_reg = Z3Reg([core_externs])
        p4_package = p4_module(z3_reg)
        if not p4_package:
            log.warning("No main module, nothing to evaluate!")
            return z3_asts, util.EXIT_SKIPPED
        z3_asts = p4_package
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


def get_z3_formulization(p4_file, out_dir=OUT_DIR):

    if p4_file.suffix == ".p4":
        util.check_dir(out_dir)
        py_file = out_dir.joinpath(p4_file.with_suffix(".py").name)
        result = run_p4_to_py(p4_file, py_file)
        p4_file = py_file
        if result.returncode != util.EXIT_SUCCESS:
            log.error("Failed to translate P4 to Python.")
            log.error("Compiler crashed!")
            return None, result.returncode

    p4py_module = get_py_module(p4_file)
    if p4py_module is None:
        return None, util.EXIT_FAILURE
    package, result = get_z3_asts(p4py_module, p4_file)
    if result != util.EXIT_SUCCESS:
        return None, result
    return package, result


def get_flat_members(names):
    flat_members = []
    for name, p4z3_obj in names:
        if isinstance(p4z3_obj, P4ComplexType):
            for sub_member in p4z3_obj.flat_names:
                flat_members.append(f"{name}.{sub_member.name}")
        else:
            flat_members.append(name)
    return flat_members


def reconstruct_input(pipe_name, package, pipe_cls):
    # these names are not quite accurate
    if isinstance(pipe_cls, P4Extern):
        initial_state = z3.Const(f"{pipe_name}", pipe_cls.z3_type)
    else:
        p4_state = package.z3_reg.set_p4_state(pipe_name, pipe_cls.params)
        initial_state = p4_state.get_z3_repr()

    inital_inputs = initial_state.children()
    return inital_inputs


def handle_nested_ifs(pipe_name, flat_members, inputs, outputs):
    cond = outputs[0]
    then_outputs = outputs[1].children()
    else_outputs = outputs[2].children()
    if z3.z3util.is_app_of(outputs[1], z3.Z3_OP_ITE):
        handle_nested_ifs(pipe_name, flat_members, inputs, then_outputs)
    else:
        zipped_list = zip(flat_members, inputs, then_outputs)
        table = tabulate(zipped_list, headers=["NAME", "INPUT", "OUTPUT"])
        log.info("PIPE %s Condition:\n\"%s\"\n%s\n", pipe_name, cond, table)
        zipped_list = zip(flat_members, inputs, then_outputs)

    if z3.z3util.is_app_of(outputs[2], z3.Z3_OP_ITE):
        handle_nested_ifs(pipe_name, flat_members, inputs, else_outputs)
    else:
        zipped_list = zip(flat_members, inputs, else_outputs)
        table = tabulate(zipped_list, headers=["NAME", "INPUT", "OUTPUT"])
        log.info("PIPE %s Condition:\n\"%s\"\n%s\n",
                 pipe_name, z3.Not(cond), table)
        zipped_list = zip(flat_members, inputs, else_outputs)


def print_z3_data(pipe_name, pipe_val, package):
    z3_datatype, p4_z3_objs, pipe_cls = pipe_val
    z3_datatype = z3.simplify(z3_datatype)
    flat_members = get_flat_members(p4_z3_objs)
    inputs = reconstruct_input(pipe_name, package, pipe_cls)
    outputs = z3_datatype.children()
    if z3.z3util.is_app_of(z3_datatype, z3.Z3_OP_ITE):
        handle_nested_ifs(pipe_name, flat_members, inputs, outputs)
    else:
        zipped_list = zip(flat_members, inputs, outputs)
        table = tabulate(zipped_list, headers=["NAME", "INPUT", "OUTPUT"])
        log.info("PIPE %s:\n%s\n", pipe_name, table)
    # log.info("%-20s %-20s %-20s" % ("NAME", "INPUT", "OUTPUT"))
    # log.info("-" * 60)
    # w = max([max(len(str(x)) for x in col) for col in zipped_list])
    # zipped_list = zip(flat_members, inputs, outputs)
    # for name, input, output in zipped_list:
    #     row = f"{name: <{w}} {str(input): <{w}} {str(output): <{w}}"
    #     log.info(row)


def main(args=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--p4_input", dest="p4_input", default=None,
                        type=lambda x: util.is_valid_file(parser, x),
                        help="The main input p4 file. This can either be a P4"
                        " program or the Python ToZ3 IR.")
    parser.add_argument("-o", "--out_dir", dest="out_dir",
                        default=OUT_DIR,
                        help="Where intermediate output is stored.")
    args = parser.parse_args(args)
    package, result = get_z3_formulization(args.p4_input, Path(args.out_dir))
    if result == util.EXIT_SUCCESS:
        for pipe_name, pipe_val in package.get_pipes().items():
            print_z3_data(pipe_name, pipe_val, package)
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
