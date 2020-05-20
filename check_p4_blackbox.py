import argparse
import logging
import time
import math
import os
import sys
import itertools
import signal
from pathlib import Path
from dataclasses import dataclass


import z3
import p4z3.util as util
import check_p4_pair as z3check


log = logging.getLogger(__name__)

FILE_DIR = Path(__file__).parent.resolve()
P4Z3_BIN = FILE_DIR.joinpath("p4c/build/p4toz3")
P4RANDOM_BIN = FILE_DIR.joinpath("p4c/build/p4bludgeon")
OUT_DIR = FILE_DIR.joinpath("validated")
P4C_DIR = FILE_DIR.joinpath("p4c")
TOFINO_DIR = FILE_DIR.joinpath("tofino/bf_src")

# signifies an invalid header
INVALID_VAR = "invalid"
# the main input header key word
HEADER_VAR = "Headers"


@dataclass
class P4Struct:
    name: str
    values: list


def generate_random_prog(p4c_bin, p4_file, config):
    p4_cmd = f"{p4c_bin} "
    p4_cmd += f"{p4_file} "
    if config["use_tofino"]:
        p4_cmd += f"1 "
    else:
        p4_cmd += f"0 "
    log.info("Generating random p4 code with command %s ", p4_cmd)
    return util.exec_process(p4_cmd)


def run_p4_to_py(p4_file, py_file, config, option_str=""):
    cmd = f"{P4Z3_BIN} "
    cmd += f"{p4_file} "
    cmd += f"--output {py_file} "
    cmd += option_str
    if config["use_tofino"]:
        include_dir = TOFINO_DIR.joinpath(f"install/share/p4c/p4include/ ")
        cmd += f"-I {include_dir}"
    log.info("Converting p4 to z3 python with command %s ", cmd)
    return util.exec_process(cmd)


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
            hex_str = f"{bitvec_val:0{bitvec_hex_width}X}"
            input_values.append(hex_str)
        else:
            raise RuntimeError(f"Type {type(val)} not supported!")
    return input_values


# https://stackoverflow.com/questions/14141977/check-if-a-formula-is-a-term-in-z3py
CONNECTIVE_OPS = [z3.Z3_OP_NOT, z3.Z3_OP_AND, z3.Z3_OP_OR, z3.Z3_OP_XOR,
                  z3.Z3_OP_IMPLIES, z3.Z3_OP_IFF, z3.Z3_OP_ITE]
REL_OPS = [z3.Z3_OP_EQ, z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT]
ALL_OPS = CONNECTIVE_OPS + REL_OPS


def get_branch_conditions(z3_formula):
    conditions = set()
    if z3_formula.decl().kind() in REL_OPS:
        # FIXME: This does not unroll if statements
        # This could lead to conflicting formulas
        conditions.add(z3_formula)
    for child in z3_formula.children():
        sub_conds = get_branch_conditions(child)
        conditions |= sub_conds
    return conditions


def convert_to_stf(input_values, input_name, append_values=False):
    stf_lst = []
    for val in input_values:
        if isinstance(val, P4Struct):
            if val.name == input_name:
                stf_lst.extend(convert_to_stf(val.values, input_name, True))
            else:
                stf_lst.extend(convert_to_stf(
                    val.values, input_name, append_values))
        elif isinstance(val, str):
            if append_values:
                stf_lst.extend(list(val))
        else:
            raise RuntimeError(f"Type {type(val)} not supported!")
    return stf_lst


def insert_spaces(text, dist):
    return " ".join(text[i:i + dist] for i in range(0, len(text), dist))


def get_stf_str(config, z3_model, z3_const, dont_care_map):
    z3_input_header = z3_model[z3.Const(
        config["ingress_var"], z3_const.sort())]
    log.debug("Input header: %s", z3_input_header)
    input_values = fill_values(z3_input_header)
    input_pkt_str = "".join(convert_to_stf(input_values, HEADER_VAR))
    z3_output_header = z3_model[z3_const]
    log.debug("Output header: %s", z3_output_header)
    output_values = fill_values(z3_output_header)
    out_pkt_list = convert_to_stf(output_values, HEADER_VAR)
    for idx, marker in enumerate(dont_care_map):
        # this is an uninterpreted value, it can be anything
        if marker == "*":
            out_pkt_list[idx] = "*"
        # this means that these bytes should be removed
        # since the header is marked as invalid
        elif marker == "x":
            out_pkt_list[idx] = ""
    output_pkt_str = "".join(out_pkt_list)
    stf_str = "packet 0 "
    stf_str += insert_spaces(input_pkt_str, 2)
    stf_str += "\nexpect 0 "
    stf_str += insert_spaces(output_pkt_str, 2)
    return stf_str


def get_semantics(config):
    p4_input = config["p4_input"]
    out_dir = config["out_dir"]
    py_file = Path(f"{out_dir}/{p4_input.stem}.py")
    fail_dir = out_dir.joinpath("failed")

    result = run_p4_to_py(p4_input, py_file, config)
    if result.returncode != util.EXIT_SUCCESS:
        log.error("Failed to translate P4 to Python.")
        util.check_dir(fail_dir)
        with open(f"{fail_dir}/error.txt", 'w+') as err_file:
            err_file.write(result.stderr.decode("utf-8"))
        util.copy_file([p4_input, py_file], fail_dir)
        return None, result.returncode
    z3_prog, result = z3check.get_z3_formulization(py_file, fail_dir)
    if result != util.EXIT_SUCCESS:
        return None, result
    return z3_prog, util.EXIT_SUCCESS


def run_bmv2_test(out_dir, p4_input):
    cmd = "python3 "
    cmd += f"{P4C_DIR}/backends/bmv2/run-bmv2-test.py "
    cmd += f"{P4C_DIR} -v "
    cmd += f"-bd {P4C_DIR}/build "
    cmd += f"{out_dir}/{p4_input.name} "
    test_proc = util.start_process(cmd, cwd=out_dir)

    def signal_handler(sig, frame):
        log.warning("run_tofino_test: Caught Interrupt, exiting...")
        os.kill(test_proc.pid, signal.SIGINT)
        sys.exit(1)
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)

    stdout, stderr = test_proc.communicate()

    return test_proc, stdout, stderr


def cleanup(procs):
    for proc in procs:
        os.killpg(os.getpgid(proc.pid), signal.SIGTERM)


def save_error(err_path, stdout, stderr):
    log.error("*" * 60)
    log.error(stdout.decode("utf-8"))
    log.error("*" * 60)
    log.error(stderr.decode("utf-8"))
    log.error("*" * 60)
    util.check_dir(err_path.parent)
    with open(f"{err_path}", 'w+') as err_file:
        err_file.write(stdout.decode("utf-8"))
        err_file.write(stderr.decode("utf-8"))


def run_tofino_test(out_dir, p4_input, stf_file_name):
    # we need to change the working directory
    # tofino scripts make some assumptions where to dump files
    prog_name = p4_input.stem
    # we need to create a specific test dir in which we can run tests
    test_dir = out_dir.joinpath("test_dir")
    util.check_dir(test_dir)
    util.copy_file(stf_file_name, test_dir)
    template_name = test_dir.joinpath(f"{prog_name}.py")
    # use a test template that runs stf tests
    util.copy_file(f"{FILE_DIR}/tofino_test_template.py", template_name)

    # initialize the target install
    log.info("Building the tofino target...")
    config_cmd = f"{TOFINO_DIR}/pkgsrc/p4-build/configure "
    config_cmd += f"--with-tofino --with-p4c=bf-p4c "
    config_cmd += f"--prefix={TOFINO_DIR}/install "
    config_cmd += f"--bindir={TOFINO_DIR}/install/bin "
    config_cmd += f"P4_NAME={prog_name} "
    config_cmd += f"P4_PATH={p4_input.resolve()} "
    config_cmd += f"P4_VERSION=p4-16 "
    config_cmd += f"P4_ARCHITECTURE=tna "
    result = util.exec_process(config_cmd, cwd=out_dir)
    if result.returncode != util.EXIT_SUCCESS:
        return result, result.stdout, result.stderr
    # create the target
    make_cmd = f"make -C {out_dir} "
    result = util.exec_process(make_cmd)
    if result.returncode != util.EXIT_SUCCESS:
        return result, result.stdout, result.stderr
    # install the target in the tofino folder
    make_cmd = f"make install -C {out_dir} "
    result = util.exec_process(make_cmd)
    if result.returncode != util.EXIT_SUCCESS:
        return result, result.stdout, result.stderr
    procs = []
    test_proc = None
    # start the target in the background
    log.info("Starting the tofino model...")
    os_env = os.environ.copy()
    os_env["SDE"] = f"{TOFINO_DIR}"
    os_env["SDE_INSTALL"] = f"{TOFINO_DIR}/install"

    model_cmd = f"{TOFINO_DIR}/run_tofino_model.sh "
    model_cmd += f"-p {prog_name} "
    proc = util.start_process(
        model_cmd, preexec_fn=os.setsid, env=os_env, cwd=out_dir)
    procs.append(proc)
    # start the binary for the target in the background
    log.info("Launching switchd...")
    os_env = os.environ.copy()
    os_env["SDE"] = f"{TOFINO_DIR}"
    os_env["SDE_INSTALL"] = f"{TOFINO_DIR}/install"

    switch_cmd = f"{TOFINO_DIR}/run_switchd.sh "
    switch_cmd += f"--arch tofino "
    switch_cmd += f"-p {prog_name} "
    proc = util.start_process(
        switch_cmd, preexec_fn=os.setsid, env=os_env, cwd=out_dir)
    procs.append(proc)

    # wait for a bit
    time.sleep(2)
    # finally we can run the test
    log.info("Running the actual test...")
    test_cmd = f"{TOFINO_DIR}/run_p4_tests.sh "
    test_cmd += f"-t {test_dir} "
    os_env = os.environ.copy()
    os_env["SDE"] = f"{TOFINO_DIR}"
    os_env["SDE_INSTALL"] = f"{TOFINO_DIR}/install"
    os_env["PYTHONPATH"] = f"${{PYTHONPATH}}:{FILE_DIR}"
    test_proc = util.start_process(test_cmd, env=os_env, cwd=out_dir)

    def signal_handler(sig, frame):
        log.warning("run_tofino_test: Caught Interrupt, exiting...")
        cleanup(procs)
        os.kill(test_proc.pid, signal.SIGINT)
        os.kill(test_proc.pid, signal.SIGTERM)
        sys.exit(1)
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)

    stdout, stderr = test_proc.communicate()
    cleanup(procs)
    return test_proc, stdout, stderr


def run_stf_test(config, stf_str):
    out_dir = config["out_dir"]
    p4_input = config["p4_input"]
    log.info("Running stf test on file %s", p4_input)

    fail_dir = out_dir.joinpath("failed")
    stf_file_name = out_dir.joinpath(f"{p4_input.stem}.stf")
    with open(stf_file_name, 'w+') as stf_file:
        stf_file.write(stf_str)
    if config["use_tofino"]:
        result, stdout, stderr = run_tofino_test(
            out_dir, p4_input, stf_file_name)
    else:
        result, stdout, stderr = run_bmv2_test(out_dir, p4_input)
    if result.returncode != util.EXIT_SUCCESS:
        log.error("Failed to validate %s with a stf test:", p4_input.name)
        err_file = Path(f"{fail_dir}/{p4_input.stem}_error.txt")
        save_error(err_file, stdout, stderr)
    else:
        log.info("Validation of %s with an stf test succeeded.", p4_input.name)
    return result.returncode


def check_with_stf(config, model, output_const, dont_care_map):
    # both the input and the output variable are then used to generate
    # a stf file with an input and expected output packet on port 0
    log.info("Generating stf file...")
    stf_str = get_stf_str(config, model, output_const, dont_care_map)
    return run_stf_test(config, stf_str)


def assemble_dont_care_map(z3_input, dont_care_vals):
    dont_care_map = []
    for var in z3_input.children():
        if isinstance(var, z3.DatatypeRef):
            dont_care_map.extend(assemble_dont_care_map(var, dont_care_vals))
        elif isinstance(var, z3.BitVecRef):
            bitvec_hex_width = math.ceil(var.size() / 4)
            dont_care = False
            for dont_care_val in dont_care_vals:
                if dont_care_val in str(var):
                    dont_care = True
            if str(var) == INVALID_VAR:
                bitvec_map = ["x"] * bitvec_hex_width
            elif dont_care:
                bitvec_map = ["*"] * bitvec_hex_width
            else:
                bitvec_map = ["."] * bitvec_hex_width
            dont_care_map.extend(bitvec_map)
        else:
            raise RuntimeError(f"Type {type(var)} not supported!")
    return dont_care_map


def get_dont_care_map(config, z3_input):
    for child in z3_input.children():
        if HEADER_VAR in child.sort().name():
            dont_care_vals = set()
            for val in z3.z3util.get_vars(z3_input):
                str_val = str(val)
                # both of these strings are special
                # ingress means it is a variable we have control over
                # invalid means that there is no byte output
                if str(val) not in (config["ingress_var"], INVALID_VAR):
                    dont_care_vals.add(str_val)
            return assemble_dont_care_map(child, dont_care_vals)
        else:
            dont_care_map = get_dont_care_map(config, child)
            if dont_care_map:
                return dont_care_map
    return []


def dissect_conds(config, conditions):
    controllable_conds = []
    avoid_conds = []
    undefined_conds = []
    undefined_vars = []
    for cond in conditions:
        cond = z3.simplify(cond)
        has_member = False
        has_table_key = False
        has_table_action = False
        has_undefined_var = False
        for cond_var in z3.z3util.get_vars(cond):
            if config["ingress_var"] in str(cond_var):
                has_member = True
            elif "table_key" in str(cond_var):
                has_table_key = True
            elif "action" in str(cond_var):
                has_table_action = True
            else:
                undefined_vars.append(cond_var)
                has_undefined_var = True
        if has_member and not (has_table_key or has_table_action or has_undefined_var):
            controllable_conds.append(cond)
        elif has_undefined_var and not (has_table_key or has_table_action):
            pass
        else:
            avoid_conds.append(cond)
    for var in undefined_vars:
        # FIXME: does not handle undefined data types
        if isinstance(var, z3.BitVecRef):
            undefined_conds.append(var == 0)
        elif isinstance(var, z3.BoolRef):
            undefined_conds.append(var == False)
    return controllable_conds, avoid_conds, undefined_conds


def perform_blackbox_test(config):
    out_dir = config["out_dir"]
    p4_input = config["p4_input"]
    if out_dir == OUT_DIR:
        out_dir = out_dir.joinpath(p4_input.stem)
    util.check_dir(out_dir)
    util.copy_file(p4_input, out_dir)
    config["out_dir"] = out_dir
    config["p4_input"] = p4_input

    # get the semantic representation of the original program
    z3_main_prog, result = get_semantics(config)
    if result != util.EXIT_SUCCESS:
        return result
    # now we actually verify that we can find an input
    s = z3.Solver()
    # we currently ignore all other pipelines and focus on the ingress pipeline
    main_formula = z3.simplify(z3_main_prog[config["pipe_name"]])
    # this util might come in handy later.
    # z3.z3util.get_vars(main_formula)
    conditions = get_branch_conditions(main_formula)
    log.info(conditions)
    cond_tuple = dissect_conds(config, conditions)
    permut_conds, avoid_conds, undefined_conds = cond_tuple
    log.info("Computing permutations...")
    # FIXME: This does not scale well...
    # FIXME: This is a complete hack, use a more sophisticated method
    permuts = [[f(var) for var, f in zip(permut_conds, x)]
               for x in itertools.product([z3.Not, lambda x: x],
                                          repeat=len(permut_conds))]
    output_const = z3.Const("output", main_formula.sort())
    # bind the output constant to the output of the main program
    s.add(main_formula == output_const)
    # all keys must be false for now
    # FIXME: Some of them should be usable
    log.info(15 * "#")
    log.info("Undefined conditions:")
    s.add(z3.And(*undefined_conds))
    for cond in undefined_conds:
        log.info(cond)
    log.info("Conditions to avoid:")
    s.add(z3.Not(z3.Or(*avoid_conds)))
    for cond in avoid_conds:
        log.info(cond)
    log.info("Permissible permutations:")
    for cond in permuts:
        log.info(cond)
    log.info(15 * "#")
    for permut in permuts:
        s.push()
        s.add(permut)
        log.info("Checking for solution...")
        ret = s.check()
        if ret == z3.sat:
            log.info("Found a solution!")
            # get the model
            m = s.model()
            # this does not work well yet... desperate hack
            # FIXME: Figure out a way to solve this, might not be solvable
            avoid_matches = z3.Not(z3.Or(*avoid_conds))
            undefined_matches = z3.And(*undefined_conds)
            permut_match = z3.And(*permut)
            g = z3.Goal()
            g.add(main_formula == output_const,
                  avoid_matches, undefined_matches, permut_match)
            log.debug(z3.tactics())
            t = z3.Then(
                z3.Tactic("propagate-values"),
                z3.Tactic("ctx-solver-simplify"),
                z3.Tactic("elim-and")
            )
            log.info("Inferring simplified input and output")
            constrained_output = t.apply(g)
            log.info("Inferring dont-care map...")
            output_var = constrained_output[0][0]
            dont_care_map = get_dont_care_map(config, output_var)
            result = check_with_stf(config, m, output_const, dont_care_map)
            if result != util.EXIT_SUCCESS:
                return result
        else:
            # FIXME: This should be an error
            log.warning("No valid input could be found!")
        s.pop()
    return result


def main(args):
    # configure logging
    logging.basicConfig(filename=args.log_file,
                        format="%(levelname)s:%(message)s",
                        level=logging.INFO,
                        filemode='w')
    stderr_log = logging.StreamHandler()
    stderr_log.setFormatter(logging.Formatter("%(levelname)s:%(message)s"))
    logging.getLogger().addHandler(stderr_log)

    if args.randomize_input:
        z3.set_param("smt.phase_selection", 5,
                     "smt.arith.random_initial_value", True,
                     "sat.phase", "random",)

    config = {}
    config["use_tofino"] = args.use_tofino
    if args.use_tofino:
        config["pipe_name"] = "Pipeline_ingress"
        config["ingress_var"] = "ingress"
    else:
        config["pipe_name"] = "ig"
        config["ingress_var"] = "ig"

    if args.p4_input:
        p4_input = Path(args.p4_input)
        out_base_dir = Path(args.out_dir)
    else:
        out_base_dir = Path(args.out_dir).joinpath("rnd_test")
        util.check_dir(out_base_dir)
        p4_input = out_base_dir.joinpath("rnd_test.p4")
        # generate a random program from scratch
        generate_random_prog(P4RANDOM_BIN, p4_input, config)

    if os.path.isfile(p4_input):
        out_dir = out_base_dir.joinpath(p4_input.stem)
        util.del_dir(out_dir)
        config["out_dir"] = out_dir
        config["p4_input"] = p4_input
        result = perform_blackbox_test(config)
    else:
        util.check_dir(out_base_dir)
        for p4_file in list(p4_input.glob("**/*.p4")):
            out_dir = out_base_dir.joinpath(p4_file.stem)
            util.del_dir(out_dir)
            config["out_dir"] = out_dir
            config["p4_input"] = p4_file
            result = perform_blackbox_test(config)
    sys.exit(result)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--p4_input", dest="p4_input", default=None,
                        type=lambda x: util.is_valid_file(parser, x),
                        help="The main reference p4 file.")
    parser.add_argument("--tofino", "-t", dest="use_tofino",
                        action='store_true',
                        help="Use the Tofino compiler instead of P4C.")
    parser.add_argument("-o", "--out_dir", dest="out_dir", default=OUT_DIR,
                        help="The output folder where all passes are dumped.")
    parser.add_argument("-l", "--log_file", dest="log_file",
                        default="blackbox.log",
                        help="Specifies name of the log file.")
    parser.add_argument("-r", "--randomize-input", dest="randomize_input",
                        action='store_true',
                        help="Whether to randomize the z3 input variables.")
    # Parse options and process argv
    args = parser.parse_args()
    main(args)
