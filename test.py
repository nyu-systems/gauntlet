import logging
from pathlib import Path

import pytest
import src.p4z3.util as util
import src.validate_p4_translation as tv_check
import src.check_p4_pair as z3_check
import warnings

# configure logging
log = logging.getLogger(__name__)
logging.basicConfig(filename="test.log",
                    format="%(levelname)s:%(message)s",
                    level=logging.INFO,
                    filemode='w')
stderr_log = logging.StreamHandler()
stderr_log.setFormatter(logging.Formatter("%(levelname)s:%(message)s"))
logging.getLogger().addHandler(stderr_log)

# some folder definitions
FILE_DIR = Path.resolve(Path(__file__)).parent
TEST_DIR = FILE_DIR.joinpath("tests")
TARGET_DIR = FILE_DIR.joinpath("generated")
VIOLATION_DIR = TEST_DIR.joinpath("violated")
FALSE_FRIENDS_DIR = TEST_DIR.joinpath("false_friends")
UNDEFINED_DIR = TEST_DIR.joinpath("undef_violated")
P4_DIR = FILE_DIR.joinpath("modules/p4c/testdata/p4_16_samples/")
# p4c binaries
P4C_BIN = FILE_DIR.joinpath("modules/p4c/build/p4test")

# ***** P4-16 Standard Tests *****

# these tests show pathological behavior and can currently not be tested
bad_tests = [
    "parser-unroll-switch_20160512.p4",  # does not terminate
    "parser-unroll-test1.p4",  # does not terminate
    "parser-unroll-test2.p4",  # does not terminate
    "parser-unroll-test3.p4",  # does not terminate
    "parser-unroll-test4.p4",  # does not terminate
]
# create a list of all the programs in the p4c test folder
p416_tests = set()

# this test is in a custom directory, we need to add it manually
# p416_tests.add("fabric_20190420/fabric.p4")

# we only go one level deep
for test in list(P4_DIR.glob("*.p4")):
    name = test.name
    if name in bad_tests:
        continue
    p416_tests.add(name)

# ***** tests that should trigger a violation bug *****

# these programs show pathological behavior and can currently not be tested
violation_filter = [
    "parser_loop",  # needs some work around undefined behavior
    "2314_regression",
    "2591_regression",
    "basic_routing_stripped",
    "const_entries",
]
violation_tests = set()
for test in list(VIOLATION_DIR.glob("*")):
    name = test.name
    if name in violation_filter:
        continue
    violation_tests.add(name)

# ***** tests that should *NOT* trigger a violation bug or fail*****

# these programs show pathological behavior and can currently not be tested
false_friends_filter = [
    "extern_arguments_2.p4",  # exit return value name
    "extern_arguments_3.p4",  # exit return value name
    "infinite_loop.p4",  # how to evaluate the output of an infinite loop?
    "bounded_loop.p4",  # how to handle this difference in undef behavior?
    "petr4_issue235.p4",
]

false_friends = set()
for test in list(FALSE_FRIENDS_DIR.glob("*")):
    name = test.name
    if name in false_friends_filter:
        continue
    false_friends.add(name)

# ***** tests that should *NOT* trigger a violation bug when allow_undefined
# is enabled*****

# these programs show pathological behavior and can currently not be tested
undefined_filter = [
    "NestedStructs_1",  # this actually does not throw an undefined error now
    "NestedStructs_2",  # this actually does not throw an undefined error now
    "Inline_1",
    "Inline_2",
    "Inline_3",
    "Inline_4",
    "Inline_5",
    "Inline_6",
    "simple",
]

undefined_tests = set()
for test in list(UNDEFINED_DIR.glob("*")):
    name = test.name
    if name in undefined_filter:
        continue
    undefined_tests.add(name)

# ***** broken tests, need fixing *****
xfails = [
    "complex2.p4",  # runtime index, now idea how to resolve this madness
    "issue1334.p4",  # overloading, this test should normally not be skipped
    "shadow-after-use.p4",  # very specific shadowing
    "tuple3.p4",  # not implemented yet
    "tuple4.p4",  # not implemented yet
    "actionAnnotations.p4",
    "action_fwd_ubpf.p4",
    "alias.p4",
    "annotations.p4",
    "apply-cf.p4",
    "arch1.p4",
    "arch2.p4",
    "arch3.p4",
    "arith1-bmv2.p4",
    "arith2-bmv2.p4",
    "assign.p4",
    "basic2-bmv2.p4",
    "basic_routing-bmv2.p4",
    "bfd_offload.p4",
    "bitExtract.p4",
    "bitwise-and.p4",
    "bitwise-cast.p4",
    "bool_cast.p4",
    "bool_ebpf.p4",
    "bvec_union-bmv2.p4",
    "call.p4",
    "cases.p4",
    "cast-call.p4",
    "cast.p4",
    "cast_noop.p4",
    "checksum-l4-bmv2.p4",
    "checksum1-bmv2.p4",
    "checksum2-bmv2.p4",
    "checksum3-bmv2.p4",
    "concat-fold.p4",
    "const.p4",
    "constant-in-calculation-bmv2.p4",
    "constant_folding.p4",
    "constants.p4",
    "constructor_cast.p4",
    "constsigned.p4",
    "control-as-param.p4",
    "crash-typechecker.p4",
    "crc32-bmv2.p4",
    "custom-type-restricted-fields.p4",
    "decl.p4",
    "default-package-argument.p4",
    "default-switch.p4",
    "direct-call.p4",
    "direct-call1.p4",
    "direct-call2.p4",
    "empty.p4",
    "emptyTuple.p4",
    "enum-bmv2.p4",
    "enum-folding.p4",
    "enum.p4",
    "enumCast.p4",
    "ex1.p4",
    "expression.p4",
    "extern2.p4",
    "extern3.p4",
    "fabric_20190420/fabric.p4",
    "filter.p4",
    "flowlet_switching-bmv2.p4",
    "fold_match.p4",
    "functors6.p4",
    "functors7.p4",
    "functors8.p4",
    "functors9.p4",
    "generic-struct-tuple.p4",
    "generic-struct.p4",
    "generic.p4",
    "generic1.p4",
    "hash-bmv2.p4",
    "hashext.p4",
    "hashext2.p4",
    "header-bool-bmv2.p4",
    "header-stack-ops-bmv2.p4",
    "header.p4",
    "initializer.p4",
    "inline-bmv2.p4",
    "inline-control.p4",
    "inline-control1.p4",
    "inline1-bmv2.p4",
    "intType.p4",
    "interface2.p4",
    "ipv6-switch-ml-bmv2.p4",
    "issue-2123.p4",
    "issue1025-bmv2.p4",
    "issue1049-bmv2.p4",
    "issue1062-1-bmv2.p4",
    "issue1062-bmv2.p4",
    "issue1079-bmv2.p4",
    "issue1097-2-bmv2.p4",
    "issue1097-bmv2.p4",
    "issue1107.p4",
    "issue1160.p4",
    "issue1172.p4",
    "issue1208-1.p4",
    "issue1304.p4",
    "issue1325-bmv2.p4",
    "issue1333.p4",
    "issue134-bmv2.p4",
    "issue1342.p4",
    "issue1352-bmv2.p4",
    "issue1517-bmv2.p4",
    "issue1520-bmv2.p4",
    "issue1524.p4",
    "issue1535.p4",
    "issue1540.p4",
    "issue1566-bmv2.p4",
    "issue1566.p4",
    "issue1586.p4",
    "issue1638.p4",
    "issue1653-complex-bmv2.p4",
    "issue1717.p4",
    "issue1724.p4",
    "issue1739-bmv2.p4",
    "issue1765-1-bmv2.p4",
    "issue1765-bmv2.p4",
    "issue1814-1-bmv2.p4",
    "issue1814-bmv2.p4",
    "issue1830.p4",
    "issue1879-bmv2.p4",
    "issue1897-bmv2.p4",
    "issue1914-1.p4",
    "issue1914-2.p4",
    "issue1914.p4",
    "issue1937-1-bmv2.p4",
    "issue1937-3-bmv2.p4",
    "issue1958.p4",
    "issue1985.p4",
    "issue1997.p4",
    "issue2019-1.p4",
    "issue2019.p4",
    "issue2036-3.p4",
    "issue2037.p4",
    "issue2044-bmv2.p4",
    "issue2090.p4",
    "issue2126.p4",
    "issue2201-1-bmv2.p4",
    "issue2201-bmv2.p4",
    "issue2260-2.p4",
    "issue2265-1.p4",
    "issue2265.p4",
    "issue2273-1.p4",
    "issue2273.p4",
    "issue2283_1-bmv2.p4",
    "issue2303.p4",
    "issue2335-1.p4",
    "issue2342.p4",
    "issue2391.p4",
    "issue2444.p4",
    "issue2487.p4",
    "issue2488-bmv2.p4",
    "issue249.p4",
    "issue2492.p4",
    "issue2599.p4",
    "issue2617.p4",
    "issue2627.p4",
    "issue2630.p4",
    "issue270-bmv2.p4",
    "issue298-bmv2.p4",
    "issue313_1.p4",
    "issue313_2.p4",
    "issue344.p4",
    "issue383-bmv2.p4",
    "issue407-2.p4",
    "issue407-3.p4",
    "issue430-bmv2.p4",
    "issue447-5-bmv2.p4",
    "issue461-bmv2.p4",
    "issue47.p4",
    "issue496.p4",
    "issue529.p4",
    "issue561-1-bmv2.p4",
    "issue561-2-bmv2.p4",
    "issue561-3-bmv2.p4",
    "issue561-4-bmv2.p4",
    "issue561-5-bmv2.p4",
    "issue561-6-bmv2.p4",
    "issue561-7-bmv2.p4",
    "issue561-bmv2.p4",
    "issue561.p4",
    "issue584-1.p4",
    "issue638-1.p4",
    "issue655-bmv2.p4",
    "issue655.p4",
    "issue737-bmv2.p4",
    "issue754.p4",
    "issue803-2.p4",
    "issue803-3.p4",
    "issue803.p4",
    "issue871.p4",
    "issue940.p4",
    "issue951.p4",
    "issue982.p4",
    "kvanno.p4",
    "large.p4",
    "line.p4",
    "list-compare.p4",
    "logging.p4",
    "match.p4",
    "ml-headers.p4",
    "module.p4",
    "named-arg.p4",
    "named-arg1.p4",
    "named_meter_1-bmv2.p4",
    "named_meter_bmv2.p4",
    "names.p4",
    "nested-tuple.p4",
    "nested-tuple1.p4",
    "newtype.p4",
    "newtype1.p4",
    "newtype2.p4",
    "octal.p4",
    "p416-type-use3.p4",
    "p4rt_digest_complex.p4",
    "package.p4",
    "parse.p4",
    "pipe.p4",
    "pipeline.p4",
    "pr1363.p4",
    "pragma-action.p4",
    "pragma-deprecated.p4",
    "pragma-pkginfo.p4",
    "pragma-string.p4",
    "pragmas.p4",
    "precedence.p4",
    "psa-action-profile1.p4",
    "psa-action-profile2.p4",
    "psa-action-profile3.p4",
    "psa-action-profile4.p4",
    "psa-action-selector1.p4",
    "psa-action-selector2.p4",
    "psa-action-selector3.p4",
    "psa-basic-counter-bmv2.p4",
    "psa-counter1.p4",
    "psa-counter2.p4",
    "psa-counter3.p4",
    "psa-counter4.p4",
    "psa-counter6.p4",
    "psa-custom-type-counter-index.p4",
    "psa-drop-all-bmv2.p4",
    "psa-drop-all-corrected-bmv2.p4",
    "psa-e2e-cloning-basic-bmv2.p4",
    "psa-end-of-ingress-test-bmv2.p4",
    "psa-example-counters-bmv2.p4",
    "psa-example-digest-bmv2.p4",
    "psa-example-parser-checksum.p4",
    "psa-example-register2-bmv2.p4",
    "psa-fwd-bmv2.p4",
    "psa-hash.p4",
    "psa-i2e-cloning-basic-bmv2.p4",
    "psa-idle-timeout.p4",
    "psa-isvalid.p4",
    "psa-meter1.p4",
    "psa-meter3.p4",
    "psa-meter4.p4",
    "psa-meter5.p4",
    "psa-meter6.p4",
    "psa-meter7-bmv2.p4",
    "psa-multicast-basic-2-bmv2.p4",
    "psa-multicast-basic-bmv2.p4",
    "psa-multicast-basic-corrected-bmv2.p4",
    "psa-random.p4",
    "psa-recirculate-no-meta-bmv2.p4",
    "psa-register-complex-bmv2.p4",
    "psa-register-read-write-2-bmv2.p4",
    "psa-register-read-write-bmv2.p4",
    "psa-register1.p4",
    "psa-register2.p4",
    "psa-register3.p4",
    "psa-remove-header.p4",
    "psa-resubmit-bmv2.p4",
    "psa-table-hit-miss.p4",
    "psa-test.p4",
    "psa-top-level-assignments-bmv2.p4",
    "psa-unicast-or-drop-bmv2.p4",
    "psa-unicast-or-drop-corrected-bmv2.p4",
    "rcp.p4",
    "register-serenum.p4",
    "select-type.p4",
    "serenum-expr.p4",
    "serenum-int.p4",
    "serenum.p4",
    "shadow.p4",
    "shadow1.p4",
    "shadow3.p4",
    "shift_precendence.p4",
    "simple-firewall_ubpf.p4",
    "simplify.p4",
    "spec-ex01.p4",
    "spec-ex03.p4",
    "spec-ex04.p4",
    "spec-ex06.p4",
    "spec-ex08.p4",
    "spec-ex09.p4",
    "spec-ex12.p4",
    "spec-ex13.p4",
    "spec-ex14.p4",
    "spec-ex15.p4",
    "spec-ex16.p4",
    "spec-ex17.p4",
    "spec-ex18.p4",
    "spec-ex19.p4",
    "spec-ex20.p4",
    "spec-ex22.p4",
    "spec-ex25.p4",
    "spec-ex27.p4",
    "spec-ex29.p4",
    "spec-ex31.p4",
    "specialization.p4",
    "stack.p4",
    "strength.p4",
    "strength2.p4",
    "strength5.p4",
    "string.p4",
    "string_anno.p4",
    "struct.p4",
    "struct1.p4",
    "structured-annotation.p4",
    "switch-expression.p4",
    "table-entries-ser-enum-bmv2.p4",
    "table-entries-valid-bmv2.p4",
    "table-key-serenum.p4",
    "template.p4",
    "ternary2-bmv2.p4",
    "tuple.p4",
    "tuple0.p4",
    "tuple1.p4",
    "tuple2.p4",
    "twoPipe.p4",
    "type-params.p4",
    "ubpf_checksum_extern.p4",
    "union-bmv2.p4",
    "union-key.p4",
    "union-valid-bmv2.p4",
    "union1-bmv2.p4",
    "union2-bmv2.p4",
    "union3-bmv2.p4",
    "union4-bmv2.p4",
    "useless-cast.p4",
    "v1model-digest-containing-ser-enum.p4",
    "v1model-digest-custom-type.p4",
    "v1model-p4runtime-enumint-types1.p4",
    "v1model-p4runtime-most-types1.p4",
    "v1model-special-ops-bmv2.p4",
    "valid.p4",
    "version.p4",
    "very_simple_model.p4",
    "xor_test.p4",
]


def prep_test(p4_name, p4_dir=P4_DIR):
    p4_file = p4_dir.joinpath(p4_name)
    target_dir = TARGET_DIR.joinpath(p4_file.stem)
    util.del_dir(target_dir)
    util.check_dir(target_dir)
    return p4_file, target_dir


def run_z3p4_test(p4_file, target_dir):
    if p4_file.name in bad_tests:
        pytest.skip(f"Skipping slow test {p4_file}.")
        return util.EXIT_SKIPPED
    result = tv_check.validate_translation(p4_file,
                                           target_dir,
                                           P4C_BIN,
                                           allow_undef=True,
                                           dump_info=False)
    if result == util.EXIT_UNDEF:
        msg = "Ignored undefined behavior in %s" % p4_file
        warnings.warn(msg)
        return util.EXIT_SUCCESS
    if result == util.EXIT_SKIPPED:
        pytest.skip(f"Skipping file {p4_file}.")
    return result


def run_violation_test(test_folder, allow_undefined=True):
    src_p4_file = test_folder.joinpath("orig.p4")
    for p4_file in list(test_folder.glob("**/[0-9]*.p4")):
        result, _ = z3_check.z3_check(
            [str(src_p4_file), str(p4_file)], None, allow_undefined)
        if result != util.EXIT_VIOLATION:
            return util.EXIT_FAILURE
    return util.EXIT_SUCCESS


def run_undef_test(p4_file, target_dir):
    result = tv_check.validate_translation(p4_file, target_dir, P4C_BIN, True,
                                           False)
    if result == util.EXIT_SKIPPED:
        pytest.skip(f"Skipping file {p4_file}.")
    elif result == util.EXIT_VIOLATION:
        return util.EXIT_FAILURE
    result = tv_check.validate_translation(p4_file, target_dir, P4C_BIN, False,
                                           False)
    if result != util.EXIT_VIOLATION:
        return util.EXIT_FAILURE
    return util.EXIT_SUCCESS


@pytest.mark.run_default
@pytest.mark.parametrize("test_name", sorted(p416_tests))
def test_p4c(request, test_name, pytestconfig):
    p4_file, target_dir = prep_test(test_name)
    request.node.custom_err = run_z3p4_test(p4_file, target_dir)
    if p4_file.name in xfails and request.node.custom_err != util.EXIT_SUCCESS:
        pytest.xfail(f"Expecting {p4_file} to fail.")
    if pytestconfig.getoption('--suppress-crashes'):
        assert request.node.custom_err != util.EXIT_VIOLATION
    else:
        assert request.node.custom_err == util.EXIT_SUCCESS


@pytest.mark.run_default
@pytest.mark.parametrize("test_name", sorted(false_friends))
def test_friends(request, test_name):
    p4_file, target_dir = prep_test(test_name, FALSE_FRIENDS_DIR)
    request.node.custom_err = run_z3p4_test(p4_file, target_dir)
    assert request.node.custom_err == util.EXIT_SUCCESS


@pytest.mark.run_default
@pytest.mark.parametrize("test_folder", sorted(violation_tests))
def test_violation(test_folder):
    test_folder = VIOLATION_DIR.joinpath(test_folder)
    assert run_violation_test(test_folder, True) == util.EXIT_SUCCESS


@pytest.mark.run_default
@pytest.mark.parametrize("test_folder", sorted(undefined_tests))
def test_undef_violation(test_folder):
    test_folder = UNDEFINED_DIR.joinpath(test_folder)
    assert run_violation_test(test_folder, False) == util.EXIT_SUCCESS
    assert run_violation_test(test_folder, True) == util.EXIT_FAILURE


@pytest.mark.xfail
@pytest.mark.parametrize("test_name", xfails)
def test_xfails(request, test_name):
    p4_file, target_dir = prep_test(test_name)
    request.node.custom_err = run_z3p4_test(p4_file, target_dir)
    assert request.node.custom_err == util.EXIT_SUCCESS
