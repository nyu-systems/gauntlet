import os
import argparse
import logging
import sys
from pathlib import Path
from dataclasses import dataclass
import z3
import p4z3.util as util
import check_p4_pair as z3check

log = logging.getLogger(__name__)

FILE_DIR = os.path.dirname(os.path.abspath(__file__))
P4Z3_BIN = FILE_DIR + "/p4c/build/p4toz3"
OUT_DIR = FILE_DIR + "/validated"
P4C_DIR = FILE_DIR + "/p4c"


def run_p4_to_py(p4_file, py_file):
    cmd = P4Z3_BIN + " "
    cmd += f"{p4_file} "
    cmd += f"--output {py_file} "
    return util.exec_process(cmd)


@dataclass
class P4Struct:
    name: str
    values: list


def fill_values(z3_input):
    input_values = []
    for val in z3_input.children():
        if isinstance(val, z3.DatatypeRef):
            val_name = val.sort().name()
            val_children = fill_values(val)
            complex_val = P4Struct(val_name, val_children)
            input_values.append(complex_val)
        elif isinstance(val, z3.BitVecNumRef):
            bitvec_val = val.as_long()
            bitvec_hex_width = (val.size()) // 4
            hex_str = f"{bitvec_val:0{bitvec_hex_width}}"
            input_values.append(hex_str)
        else:
            raise RuntimeError(f"Type {type(val)} not supported!")
    return input_values


def convert_to_stf(input_values, input_name, append_values=False):
    stf_str = ""
    for val in input_values:
        if isinstance(val, P4Struct):
            if val.name == input_name:
                stf_str += convert_to_stf(
                    val.values, input_name, True)
            else:
                stf_str += convert_to_stf(
                    val.values, input_name, append_values)
        elif isinstance(val, str):
            if append_values:
                stf_str += val
        else:
            raise RuntimeError(f"Type {type(val)} not supported!")
    return stf_str


def insert_spaces(text, dist):
    return " ".join(text[i:i + dist] for i in range(0, len(text), dist))


def get_stf_str(z3_model, z3_const):
    z3_input_header = z3_model[z3_model[0]]
    input_values = fill_values(z3_input_header)
    input_pkt_str = convert_to_stf(input_values, "Parsed_packet")
    z3_output_header = z3_model[z3_const]
    output_values = fill_values(z3_output_header)
    output_pkt_str = convert_to_stf(output_values, "Parsed_packet")
    stf_str = "packet 0 "
    stf_str += insert_spaces(input_pkt_str, 2)
    stf_str += "\nexpect 0 "
    stf_str += insert_spaces(output_pkt_str, 2)
    return stf_str


def get_semantics(out_dir, p4_input):
    p4_input = Path(p4_input)
    py_file = Path(f"{out_dir}/{p4_input.stem}.py")
    fail_dir = out_dir.joinpath("failed")

    result = run_p4_to_py(p4_input, py_file)
    if result.returncode != util.EXIT_SUCCESS:
        log.error("Failed to translate P4 to Python.")
        log.error("Compiler crashed!")
        util.check_dir(fail_dir)
        with open(f"{fail_dir}/error.txt", 'w+') as err_file:
            err_file.write(result.stderr.decode("utf-8"))
        util.copy_file([p4_input, py_file], fail_dir)
        return result.returncode
    z3_prog, result = z3check.get_z3_formulization(py_file, fail_dir)
    if result != util.EXIT_SUCCESS:
        return None, result

    return z3_prog, util.EXIT_SUCCESS


def main(args):

    p4_input = Path(args.p4_input)
    out_dir = Path(args.out_dir).joinpath(p4_input.stem)
    p4_subsets = args.subsets

    z3_subsets = []
    util.check_dir(out_dir)
    z3_main_prog, result = get_semantics(out_dir, p4_input)
    if result != util.EXIT_SUCCESS:
        sys.exit(result)
    for input_prog in p4_subsets:
        z3_prog, result = get_semantics(out_dir, input_prog)
        if result != util.EXIT_SUCCESS:
            sys.exit(result)
        z3_subsets.append(z3_prog)
    util.copy_file(args.p4_input, out_dir)
    util.copy_file(p4_subsets, out_dir)

    s = z3.Solver()
    z3_formula_1 = z3_main_prog["ig"]
    z3_const = z3.Const("output", z3_formula_1.sort())
    s.add(z3_formula_1 == z3_const)
    for z3_subset_prog in z3_subsets:
        z3_formula_2 = z3_subset_prog["ig"]
        s.add(z3_formula_1 == z3_formula_2)
        s.add(z3_formula_2 == z3_const)
    sat = s.check()
    if sat:
        m = s.model()
        stf_str = get_stf_str(m, z3_const)
        stf_file_name = out_dir.joinpath(f"{p4_input.stem}.stf")
        with open(stf_file_name, 'w+') as stf_file:
            stf_file.write(stf_str)
        main_cmd = "python "
        main_cmd += f"{P4C_DIR}/backends/bmv2/run-bmv2-test.py "
        main_cmd += f"{P4C_DIR} "
        # main_cmd += f"-v -a \'--maxErrorCount 100\' \"$@\"  "
        main_cmd += f"{out_dir}/{p4_input.name} "
        result = util.exec_process(main_cmd).returncode
        for input_prog in p4_subsets:
            input_prog = Path(input_prog)
            stf_file_name = out_dir.joinpath(f"{input_prog.stem}.stf")
            with open(stf_file_name, 'w+') as stf_file:
                stf_file.write(stf_str)
            subset_cmd = "python "
            subset_cmd += f"{P4C_DIR}/backends/bmv2/run-bmv2-test.py "
            subset_cmd += f"{P4C_DIR} -v "
            # subset_cmd += f"-v -a \'--maxErrorCount 100\' \"$@\"  "
            subset_cmd += f"{out_dir}/{input_prog.name} "
            result = util.exec_process(subset_cmd)

    # for cube in s.cube():
    # s.check(cube)
    # log.info(s.model())

    sys.exit(result)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--p4_input", dest="p4_input",
                        default="p4c/testdata/p4_16_samples",
                        required=True,
                        help="The main reference p4 file.")
    parser.add_argument("--subsets", "-p", dest="subsets",
                        type=str, nargs='+', default=[],
                        help="The ordered list of programs to compare.")
    parser.add_argument("-o", "--out_dir", dest="out_dir",
                        default=OUT_DIR,
                        help="The output folder where all passes are dumped.")
    parser.add_argument("-l", "--log_file", dest="log_file",
                        default="analysis.log",
                        help="Specifies name of the log file.")
    parser.add_argument("-g", "--get_semantics", dest="get_semantics",
                        action='store_true',
                        help="Only retrieve the formal semantics of the file.")
    # Parse options and process argv
    arguments = parser.parse_args()

    # configure logging
    logging.basicConfig(filename=arguments.log_file,
                        format="%(levelname)s:%(message)s",
                        level=logging.INFO,
                        filemode='w')
    stderr_log = logging.StreamHandler()
    stderr_log.setFormatter(logging.Formatter("%(levelname)s:%(message)s"))
    logging.getLogger().addHandler(stderr_log)
    main(arguments)
