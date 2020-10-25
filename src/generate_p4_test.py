import argparse
import logging
import time
import math
import os
import sys
import itertools
import signal
from pathlib import Path


import z3
import p4z3.util as util
from get_semantics import get_z3_formulization


log = logging.getLogger(__name__)

FILE_DIR = Path(__file__).parent.resolve()
ROOT_DIR = FILE_DIR.parent
P4Z3_BIN = ROOT_DIR.joinpath("modules/p4c/build/p4toz3")
P4RANDOM_BIN = ROOT_DIR.joinpath("modules/p4c/build/p4bludgeon")
OUT_DIR = ROOT_DIR.joinpath("validated")
P4C_DIR = ROOT_DIR.joinpath("modules/p4c")
TOFINO_DIR = ROOT_DIR.joinpath("tofino/bf_src")

# signifies an invalid header
INVALID_VAR = "invalid"
# the main input header key word
HEADER_VAR = "h"


def generate_p4_prog(p4c_bin, p4_file, config):
    arch = config["arch"]
    p4_cmd = f"{p4c_bin} "
    p4_cmd += f"--output {p4_file} "
    p4_cmd += f"--arch {arch} "
    log.debug("Generating random p4 code with command %s ", p4_cmd)
    return util.exec_process(p4_cmd), p4_file


def run_p4_to_py(p4_file, py_file, config, option_str=""):
    cmd = f"{P4Z3_BIN} "
    cmd += f"{p4_file} "
    cmd += f"--output {py_file} "
    cmd += option_str
    if config["arch"] == "tna":
        include_dir = TOFINO_DIR.joinpath("install/share/p4c/p4include/ ")
        cmd += f"-I {include_dir}"
    log.info("Converting p4 to z3 python with command %s ", cmd)
    return util.exec_process(cmd)


def fill_values(flat_input):
    input_values = []
    for val in flat_input:
        if isinstance(val, z3.BitVecNumRef):
            bitvec_val = val.as_long()
            bitvec_hex_width = math.ceil(val.size() / 4)
            hex_str = f"{bitvec_val:0{bitvec_hex_width}X}"
            input_values.append(hex_str)
        else:
            raise RuntimeError(f"Type {type(val)} not supported!")
    return input_values


def convert_to_stf(input_values):
    stf_lst = []
    for val in input_values:
        if isinstance(val, str):
            stf_lst.extend(list(val))
        else:
            raise RuntimeError(f"Type {type(val)} not supported!")
    return stf_lst


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


def insert_spaces(text, dist):
    return " ".join(text[i:i + dist] for i in range(0, len(text), dist))


def overlay_dont_care_map(flat_output, dont_care_map):
    output_values = fill_values(flat_output)
    out_pkt_list = []
    for val in output_values:
        if isinstance(val, str):
            out_pkt_list.extend(list(val))
    for idx, marker in enumerate(dont_care_map):
        # this is an uninterpreted value, it can be anything
        if marker == "*":
            out_pkt_list[idx] = "*"
        # this means that these bytes should be removed
        # since the header is marked as invalid
        elif marker == "x":
            out_pkt_list[idx] = ""
    return out_pkt_list


def get_stf_str(flat_input, flat_output, dont_care_map):
    # both the input and the output variable are then used to generate
    # a stf file with an input and expected output packet on port 0
    log.info("Generating stf string...")
    input_pkt_str = "".join(fill_values(flat_input))
    flat_output = overlay_dont_care_map(flat_output, dont_care_map)
    output_pkt_str = "".join(flat_output)

    stf_str = "packet 0 "
    stf_str += insert_spaces(input_pkt_str, 2)
    if output_pkt_str:
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
    package, result = get_z3_formulization(py_file)
    z3_prog = package.get_pipes()
    if result != util.EXIT_SUCCESS:
        if fail_dir and result != util.EXIT_SKIPPED:
            util.check_dir(fail_dir)
            util.copy_file([p4_input, py_file], fail_dir)
        return z3_prog, result
    return z3_prog, util.EXIT_SUCCESS


def run_bmv2_test(out_dir, p4_input, use_psa=False):
    cmd = "python3 "
    cmd += f"{P4C_DIR}/backends/bmv2/run-bmv2-test.py "
    cmd += f"{P4C_DIR} -v "
    if use_psa:
        cmd += "-p "
    cmd += f"-bd {P4C_DIR}/build "
    cmd += f"{out_dir}/{p4_input.name} "
    test_proc = util.start_process(cmd, cwd=out_dir)

    def signal_handler(sig, frame):
        log.warning("run_bmv2_test: Caught Interrupt, exiting...")
        os.kill(test_proc.pid, signal.SIGINT)
        sys.exit(1)
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)

    stdout, stderr = test_proc.communicate()
    return test_proc, stdout, stderr


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
    config_cmd += "--with-tofino --with-p4c=bf-p4c "
    config_cmd += f"--prefix={TOFINO_DIR}/install "
    config_cmd += f"--bindir={TOFINO_DIR}/install/bin "
    config_cmd += f"P4_NAME={prog_name} "
    config_cmd += f"P4_PATH={p4_input.resolve()} "
    config_cmd += "P4_VERSION=p4-16 "
    config_cmd += "P4_ARCHITECTURE=tna "
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
    switch_cmd += "--arch tofino "
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
    # inserting this path is necessary for the tofino_test_template.py
    os_env["PYTHONPATH"] = f"${{PYTHONPATH}}:{ROOT_DIR}"
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
    if config["arch"] == "tna":
        result, stdout, stderr = run_tofino_test(
            out_dir, p4_input, stf_file_name)
    elif config["arch"] == "v1model":
        result, stdout, stderr = run_bmv2_test(out_dir, p4_input)
    elif config["arch"] == "psa":
        result, stdout, stderr = run_bmv2_test(out_dir, p4_input, use_psa=True)
    else:
        raise RuntimeError("Unsupported test arch \"%s\"!" % config["arch"])
    if result.returncode != util.EXIT_SUCCESS:
        log.error("Failed to validate %s with a stf test:", p4_input.name)
        err_file = Path(f"{fail_dir}/{p4_input.stem}_error.txt")
        save_error(err_file, stdout, stderr)
    else:
        log.info("Validation of %s with an stf test succeeded.", p4_input.name)
    return result.returncode


def assemble_dont_care_map(flat_list, dont_care_vals):
    dont_care_map = []
    for var in flat_list:
        if isinstance(var, z3.BitVecRef):
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


def get_dont_care_map(config, z3_input, pkt_range):
    dont_care_vals = set()
    for val in z3.z3util.get_vars(z3_input):
        str_val = str(val)
        # both of these strings are special
        # ingress means it is a variable we have control over
        # invalid means that there is no byte output
        if str(val) not in (config["ingress_var"], INVALID_VAR):
            dont_care_vals.add(str_val)
    flat_input = z3_input.children()[pkt_range]
    return assemble_dont_care_map(flat_input, dont_care_vals)


# https://stackoverflow.com/questions/14141977/check-if-a-formula-is-a-term-in-z3py
CONNECTIVE_OPS = [z3.Z3_OP_NOT, z3.Z3_OP_AND, z3.Z3_OP_OR, z3.Z3_OP_XOR,
                  z3.Z3_OP_IMPLIES, z3.Z3_OP_IFF, z3.Z3_OP_ITE]
REL_OPS = [z3.Z3_OP_EQ, z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT]
ALL_OPS = CONNECTIVE_OPS + REL_OPS


def get_branch_conditions(z3_formula):
    conditions = set()
    if isinstance(z3_formula, z3.BoolRef):
        # if z3_formula.decl().kind() in REL_OPS + CONNECTIVE_OPS:
        # FIXME: This does not unroll if statements
        # This could lead to conflicting formulas
        if z3_formula.decl().kind() not in CONNECTIVE_OPS:
            conditions.add(z3_formula)
    for child in z3_formula.children():
        sub_conds = get_branch_conditions(child)
        conditions |= sub_conds
    return conditions


def compute_permutations(permut_conds):
    log.info("Computing permutations...")
    # FIXME: This does not scale well...
    # FIXME: This is a complete hack, use a more sophisticated method
    permuts = [[f(var) for var, f in zip(permut_conds, x)]
               for x in itertools.product([z3.Not, lambda x: x],
                                          repeat=len(permut_conds))]
    return permuts


def dissect_conds(config, conditions):
    controllable_conds = []
    avoid_conds = []
    undefined_conds = []
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
                if "_valid" in str(cond_var):
                    # let's assume that every input header is valid
                    # we have no choice right now
                    undefined_conds.append(cond_var == True)
                else:
                    # all keys must be false for now
                    # FIXME: Some of them should be usable
                    if isinstance(cond_var, z3.BitVecRef):
                        undefined_conds.append(cond_var == 0)
                    elif isinstance(cond_var, z3.BoolRef):
                        undefined_conds.append(cond_var == False)
                has_undefined_var = True
        if has_member and not (has_table_key or has_table_action or has_undefined_var):
            controllable_conds.append(cond)
        elif has_undefined_var and not (has_table_key or has_table_action):
            pass
        else:
            avoid_conds.append(cond)

    permut_conds = compute_permutations(controllable_conds)

    log.info(15 * "#")
    log.info("Undefined conditions:")
    for cond in undefined_conds:
        log.info(cond)
    log.info("Conditions to avoid:")
    for cond in avoid_conds:
        log.info(cond)
    log.info("Permissible permutations:")
    for cond in controllable_conds:
        log.info(cond)
    log.info(15 * "#")

    return permut_conds, avoid_conds, undefined_conds


def get_main_formula(config):
    # get the semantic representation of the original program
    z3_main_prog, result = get_semantics(config)
    if result != util.EXIT_SUCCESS:
        return result
    # we currently ignore all other pipelines and focus on the ingress pipeline
    main_formula, main_map, pipe_cls = z3_main_prog[config["pipe_name"]]
    pkt_range = None
    idx = 0
    # FIXME: Make this more robust, assume HEADER_VAR is always first
    for member_name, member_type in main_map:
        if member_name == HEADER_VAR:
            pkt_range = slice(idx, idx + len(member_type.flat_names))
    if not pkt_range:
        log.error("No valid input formula found!"
                  " Check if your variable names are correct.")
        log.error(
            "This program checks for the \"%s\" variable in the pipe call.", HEADER_VAR)
        return None, None
    main_formula = z3.simplify(main_formula)
    return main_formula, pkt_range


def build_test(config, main_formula, cond_tuple, pkt_range):
    permut_conds, avoid_conds, undefined_conds = cond_tuple

    # now we actually verify that we can find an input
    s = z3.Solver()
    # bind the output constant to the output of the main program
    output_const = z3.Const("output", main_formula.sort())
    s.add(main_formula == output_const)

    undefined_matches = z3.And(*undefined_conds)
    s.add(undefined_matches)

    avoid_matches = z3.Not(z3.Or(*avoid_conds))
    s.add(avoid_matches)
    # we need this tactic to find out which values will be undefined at the end
    # or which headers we expect to be invalid
    # the tactic effectively simplifies the formula to a single expression
    # under the constraints we have defined
    t = z3.Then(
        z3.Tactic("propagate-values"),
        z3.Tactic("ctx-solver-simplify"),
        z3.Tactic("elim-and")
    )
    # this is the test string we assemble
    stf_str = ""
    for permut in permut_conds:
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
            g = z3.Goal()
            g.add(main_formula == output_const,
                  avoid_matches, undefined_matches, z3.And(*permut))
            log.debug(z3.tactics())
            log.info("Inferring simplified input and output")
            constrained_output = t.apply(g)
            log.info("Inferring dont-care map...")
            # FIXME: horrible
            output_var = constrained_output[0][0].children()[0]
            dont_care_map = get_dont_care_map(config, output_var, pkt_range)
            input_hdr = m[z3.Const(config["ingress_var"], output_const.sort())]
            output_hdr = m[output_const]
            log.debug("Output header: %s", output_hdr)
            log.debug("Input header: %s", input_hdr)
            flat_input = input_hdr.children()[pkt_range]
            flat_output = output_hdr.children()[pkt_range]
            stf_str += get_stf_str(flat_input, flat_output, dont_care_map)
            stf_str += "\n"
        else:
            # FIXME: This should be an error
            log.warning("No valid input could be found!")
        s.pop()
    # the final stf string lists all the interesting packets to test
    return stf_str


def perform_blackbox_test(config):
    out_dir = config["out_dir"]
    p4_input = config["p4_input"]
    if out_dir == OUT_DIR:
        out_dir = out_dir.joinpath(p4_input.stem)
    util.check_dir(out_dir)
    util.copy_file(p4_input, out_dir)
    config["out_dir"] = out_dir
    config["p4_input"] = p4_input

    main_formula, pkt_range = get_main_formula(config)
    if main_formula == None or not pkt_range:
        return util.EXIT_FAILURE
    conditions = set()
    # FIXME: Another hack to deal with branch conditions we cannot control
    for child in main_formula.children()[pkt_range]:
        conditions |= get_branch_conditions(child)
    cond_tuple = dissect_conds(config, conditions)
    stf_str = build_test(config, main_formula, cond_tuple, pkt_range)
    # finally, run the test with the stf string we have assembled
    # and return the result of course
    return run_stf_test(config, stf_str)


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
        seed = int.from_bytes(os.getrandom(8), "big")
        z3.set_param("smt.phase_selection", 5,
                     "smt.random_seed", seed,
                     "smt.arith.random_initial_value", True,
                     "sat.phase", "random",)

    config = {}
    config["arch"] = args.arch
    if config["arch"] == "tna":
        config["pipe_name"] = "pipe0_ingress"
        config["ingress_var"] = "ingress"
    elif config["arch"] == "v1model":
        config["pipe_name"] = "ig"
        config["ingress_var"] = "ig"
    elif config["arch"] == "psa":
        config["pipe_name"] = "ingress_ig"
        config["ingress_var"] = "ig"
    else:
        raise RuntimeError("Unsupported test arch \"%s\"!" % config["arch"])

    if args.p4_input:
        p4_input = Path(args.p4_input)
        out_base_dir = Path(args.out_dir)
    else:
        out_base_dir = Path(args.out_dir).joinpath("rnd_test")
        util.check_dir(out_base_dir)
        p4_input = out_base_dir.joinpath("rnd_test.p4")
        # generate a random program from scratch
        generate_p4_prog(P4RANDOM_BIN, p4_input, config)

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
    parser.add_argument("-a", "--arch", dest="arch", default="v1model",
                        type=str, help="Specify the back end to test.")
    parser.add_argument("-o", "--out_dir", dest="out_dir", default=OUT_DIR,
                        help="The output folder where all passes are dumped.")
    parser.add_argument("-l", "--log_file", dest="log_file",
                        default="model.log",
                        help="Specifies name of the log file.")
    parser.add_argument("-r", "--randomize-input", dest="randomize_input",
                        action='store_true',
                        help="Whether to randomize the z3 input variables.")
    # Parse options and process argv
    args = parser.parse_args()
    main(args)
