from pathlib import Path
FILE_DIR = Path(__file__).parent.resolve()
FILE_NAME = Path(__file__).stem
import ptf.testutils as testutils
from ptf import mask
from bfruntime_client_base_tests import BfRuntimeTest
from p4c.tools.stf.stf_parser import STFParser


class VerifyTest(BfRuntimeTest):
    def setUp(self):
        client_id = 0
        # the test has the same name as this template file
        BfRuntimeTest.setUp(self, client_id, FILE_NAME)

    def runTest(self):
        stf_parser = STFParser()
        # the test will have the same name as the file
        stf_file = FILE_DIR.joinpath(f"{FILE_NAME}.stf")
        parsed_stf, _ = stf_parser.parse(filename=stf_file)
        input_pkts = []
        expect_pkts = []
        for entry in parsed_stf:
            stf_class = entry[0]
            stf_port = entry[1]
            stf_bytes = entry[2]
            if stf_class == "packet":
                input_pkts.append((stf_port, stf_bytes))
            if stf_class == "expect":
                expect_pkts.append((stf_port, stf_bytes))
        for input_pkt in input_pkts:
            input_port = input_pkt[0]
            input_bytes = bytes.fromhex(input_pkt[1])
            testutils.send_packet(self, input_port, input_bytes)
        try:
            for expect_pkt in expect_pkts:
                expect_port = expect_pkt[0]
                expect_bytes = list(expect_pkt[1])
                dont_care_bits = []
                for idx, hexbit in enumerate(expect_bytes):
                    if hexbit == "*":
                        dont_care_bits.append(idx * 4)
                        expect_bytes[idx] = "0"
                expect_bytes = "".join(expect_bytes)
                expect_bytes = bytes.fromhex(expect_bytes)
                pkt = mask.Mask(expect_bytes)
                pkt.set_ignore_extra_bytes()
                for dont_care_bit in dont_care_bits:
                    pkt.set_do_not_care(dont_care_bit, 4)
                testutils.verify_packet(self, pkt, expect_port)
        except AssertionError as e:
            with open(f"{FILE_NAME}_ptf_err.log", 'w+') as err_file:
                err_file.write(str(e))
                err_file.flush()
            raise AssertionError("Test failed, see error above")
