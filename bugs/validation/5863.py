"""PTF test for P4C's standard run-dpdk-ptf-test.py runner."""

import base_test as bt
from ptf import testutils


class UnionExtraction(bt.P4RuntimeTest):
    def setUp(self):
        super().setUp()
        self.assertTrue(self.updateConfig())

    def runTest(self):
        # Both union bytes are consumed; only the result header is re-emitted.
        packet = bytes(14) + b"\x07\x08" + bytes(48)
        expected = bytes(12) + b"\x00\x01" + bytes(48)
        testutils.send_packet(self, 0, packet)
        testutils.verify_packet(self, expected, 1)
        testutils.verify_no_other_packets(self)
