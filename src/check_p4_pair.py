import argparse
from pathlib import Path
import sys
import logging
import z3

from p4z3.contrib.tabulate import tabulate
from get_semantics import get_z3_formulization
import p4z3.util as util
from p4z3 import P4ComplexType

sys.setrecursionlimit(15000)


FILE_DIR = Path(__file__).parent.resolve()
log = logging.getLogger(__name__)

# We maintain a list of passes to skip for convenience
# This reduces the amount of noise when generating random programs
SKIPPED_PASSES = []


def needs_skipping(post):
    for skip_pass in SKIPPED_PASSES:
        if skip_pass in post:
            log.warning("Skipping \"%s\" pass...", skip_pass)
            return True
    return False


def debug_msg(p4_files):
    debug_string = "You can debug this failure by running:\n"
    debug_string += f"python3 {FILE_DIR}/{Path(__file__).stem}.py --progs "
    for p4_file in p4_files:
        p4_file_name = p4_file.stem
        p4_file_dir = p4_file.parent
        debug_string += f" {p4_file_dir}/failed/{p4_file_name} "
    log.error(debug_string)


def print_validation_error(prog_before, prog_after, model):
    z3_prog_before, input_names_before, _ = prog_before
    z3_prog_after, input_names_after, _ = prog_after
    error_string = "Detected an equivalence violation!\n"
    error_string += "\nPROGRAM BEFORE\n"
    error_string += get_hdr_table(z3_prog_before, input_names_before)
    error_string += "\n\nPROGRAM AFTER\n"
    error_string += get_hdr_table(z3_prog_after, input_names_after)
    error_string += "\n\nPROPOSED INPUT BEGIN\n"
    for decl in model.decls():
        value = model[decl]
        if isinstance(value, z3.DatatypeRef):
            error_string += "HEADER %s =\n" % decl
            error_string += get_hdr_table(value, input_names_before)
        else:
            error_string += "%s = %s" % (decl, value)
        error_string += "\n--\n"
    error_string += "PROPOSED INPUT END\n"
    log.error(error_string)


def handle_pyz3_error(fail_dir, p4_file):
    util.check_dir(fail_dir)
    failed = [p4_file.with_suffix(".py"), p4_file.with_suffix(".p4")]
    util.copy_file(failed, fail_dir)


def substitute_taint(z3_expr):
    decl = z3_expr.decl()
    taint = set()
    if decl.kind() == z3.Z3_OP_ITE:
        # we need to differentiate in the case of ite statements
        cond_expr = z3_expr.children()[0]
        then_expr = z3_expr.children()[1]
        else_expr = z3_expr.children()[2]
        cond_expr, cond_taint = substitute_taint(cond_expr)
        # check if the cond expr is an ite statement after substitution
        # if the condition is tainted, do not even bother to evaluate the rest
        if cond_expr.decl().kind() != z3.Z3_OP_ITE and cond_taint:
            taint_const = z3.FreshConst(z3_expr.sort(), "taint")
            return taint_const, set([taint_const])
        # evaluate the branches
        then_expr, then_taint = substitute_taint(then_expr)
        else_expr, else_taint = substitute_taint(else_expr)
        # check if the branches are an ite statement after substitution
        then_not_ite = then_expr.decl().kind() != z3.Z3_OP_ITE
        else_not_ite = else_expr.decl().kind() != z3.Z3_OP_ITE
        if (then_not_ite and else_not_ite) and (then_taint and else_taint):
            # both branches are fully tainted, replace and return
            taint_const = z3.FreshConst(z3_expr.sort(), "taint")
            return taint_const, set([taint_const])

        # merge taints and create a new ite statement
        taint |= cond_taint | then_taint | else_taint
        if taint:
            z3_expr = z3.If(cond_expr, then_expr, else_expr)
    elif z3.is_const(z3_expr) and str(z3_expr) == "undefined":
        # the expression is tainted replace it
        # really dumb check, do not need anything else
        z3_expr = z3.FreshConst(z3_expr.sort(), "taint")
        taint.add(z3_expr)
    else:
        # remaining expressions are more complex, need to evaluate children
        child_list = z3_expr.children()
        for idx, child in enumerate(child_list):
            # iterate through members of the expr
            child, child_taint = substitute_taint(child)
            # replace entire expression if one non-ite member is tainted
            if child.decl().kind() != z3.Z3_OP_ITE and child_taint:
                # the expression is tainted replace it
                taint_const = z3.FreshConst(z3_expr.sort(), "taint")
                return taint_const, set([taint_const])
            # members might also have changed, so update
            taint |= child_taint
            child_list[idx] = child
        if taint:
            # these are unfortunately necessary because AND/OR are "special"
            if decl.kind() == z3.Z3_OP_AND:
                z3_expr = z3.And(*child_list)
            elif decl.kind() == z3.Z3_OP_OR:
                z3_expr = z3.Or(*child_list)
            else:
                z3_expr = decl(*child_list)
    return z3_expr, taint


def undef_check(solver, prog_before, prog_after):
    prog_before_children = prog_before.children()
    prog_after_children = prog_after.children()
    for idx, m_before in enumerate(prog_before_children):
        log.info("Preprocessing member %s...", idx)
        m_after = prog_after_children[idx]

        m_before, taint_vars = substitute_taint(m_before)
        m_before = z3.simplify(m_before)
        m_after = z3.simplify(m_after)
        tv_equiv = m_before != m_after
        for taint_var in taint_vars:
            if m_before.sort() == taint_var.sort():
                tv_equiv = z3.And(tv_equiv, m_before != taint_var)
        tv_equiv = z3.simplify(tv_equiv)
        # check equivalence of the modified clause
        log.debug("Checking member %s...", idx)
        log.debug("Updated equation:")
        log.debug(tv_equiv)
        ret = solver.check(tv_equiv)

        if ret == z3.sat:
            log.error("Validation holds despite undefined behavior!")
            log.error("MEMBER BEFORE\n%s", m_before)
            log.error("MEMBER AFTER\n%s", m_after)
            return ret
        elif ret == z3.unknown:
            log.error("Solution unknown! There might be a problem...")
            return ret
    return ret


def get_hdr_table(z3_datatype, p4_z3_objs):
    z3_datatype = z3.simplify(z3_datatype)
    flat_members = []
    for name, p4z3_obj in p4_z3_objs:
        if isinstance(p4z3_obj, P4ComplexType):
            for sub_member in p4z3_obj.flat_names:
                flat_members.append(f"{name}.{sub_member.name}")
        else:
            flat_members.append(name)
    outputs = z3_datatype.children()
    zipped_list = zip(flat_members, outputs)
    table = tabulate(zipped_list, headers=["NAME", "OUTPUT"])
    return table


def check_equivalence(prog_before, prog_after, allow_undef):
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same
    z3_prog_before, input_names_before, _ = prog_before
    z3_prog_after, input_names_after, _ = prog_after

    try:
        z3_prog_before = z3.simplify(z3_prog_before)
        z3_prog_after = z3.simplify(z3_prog_after)
        # the equivalence equation
        log.debug("Simplifying equation...")
        tv_equiv = z3.simplify(z3_prog_before != z3_prog_after)
    except z3.Z3Exception as e:
        # Encountered an exception when trying to compare the formulas
        # There might be many reasons for this
        error_string = "Failed to compare Z3 formulas!\nReason: %s" % e
        error_string += "\nPROGRAM BEFORE\n"
        error_string += get_hdr_table(z3_prog_before, input_names_before)
        error_string += "\n\nPROGRAM AFTER\n"
        error_string += get_hdr_table(z3_prog_after, input_names_after)
        log.error(error_string)
        return util.EXIT_VIOLATION
    log.debug("Checking...")
    log.debug(z3.tactics())
    t = z3.Then(
        z3.Tactic("simplify"),
        # z3.Tactic("distribute-forall"),
        # z3.Tactic("ackermannize_bv"),
        # z3.Tactic("bvarray2uf"),
        # z3.Tactic("card2bv"),
        # z3.Tactic("propagate-bv-bounds-new"),
        # z3.Tactic("reduce-bv-size"),
        # z3.Tactic("qe_rec"),
        z3.Tactic("smt"),
    )

    solver = t.solver()
    log.debug(solver.sexpr())
    ret = solver.check(tv_equiv)
    log.debug(tv_equiv)
    log.debug(ret)
    if allow_undef and ret == z3.sat:
        # if we allow undefined changes we need to explicitly recheck
        log.info("Detected difference in undefined behavior. "
                 "Rechecking while substituting undefined variables.")
        ret = undef_check(solver, z3_prog_before, z3_prog_after)

    if ret == z3.sat:
        print_validation_error(prog_before, prog_after, solver.model())
        return util.EXIT_VIOLATION
    elif ret == z3.unknown:
        log.error("Solution unknown! There might be a problem...")
        return util.EXIT_VIOLATION
    else:
        return util.EXIT_SUCCESS


def z3_check(prog_paths, fail_dir=None, allow_undef=False):
    if len(prog_paths) < 2:
        log.error("Equivalence checks require at least two input programs!")
        return util.EXIT_FAILURE
    z3_progs = []
    for p4_prog in prog_paths:
        p4_path = Path(p4_prog)
        package, result = get_z3_formulization(p4_path)
        if result != util.EXIT_SUCCESS:
            if fail_dir and result != util.EXIT_SKIPPED:
                handle_pyz3_error(fail_dir, p4_path)
                debug_msg([p4_path, p4_path])
            return result
        pipes = package.get_pipes()
        z3_progs.append((p4_path, pipes))
    for idx in range(1, len(z3_progs)):
        p4_pre_path, pipes_pre = z3_progs[idx - 1]
        p4_post_path, pipes_post = z3_progs[idx]
        log.info("\nComparing programs\n%s\n%s\n########",
                 p4_pre_path.stem, p4_post_path.stem)
        # sometimes we want to skip a specific pass
        if needs_skipping(str(p4_post_path)):
            continue
        if len(pipes_pre) != len(pipes_post):
            log.warning("Pre and post model differ in size!")
            return util.EXIT_SKIPPED
        for pipe_name in pipes_pre:
            pipe_pre = pipes_pre[pipe_name]
            pipe_post = pipes_post[pipe_name]
            log.info("Checking z3 equivalence for pipe %s...", pipe_name)
            ret = check_equivalence(pipe_pre, pipe_post, allow_undef)
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
    parser.add_argument("-u", "--allow_undefined", dest="allow_undef",
                        action="store_true",
                        help="Ignore changes in undefined behavior.")
    args = parser.parse_args(args)
    return z3_check(args.progs, None, args.allow_undef)


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
