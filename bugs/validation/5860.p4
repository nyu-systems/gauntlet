#include <core.p4>
#include <v1model.p4>

header Result { bit<8> code; }
header H { bit<8> x; varbit<8> data; }
struct Headers { Result result; H[1] stack; }
struct Meta {}

parser P(packet_in packet, out Headers h, inout Meta m, inout standard_metadata_t sm) {
    state start {
        packet.extract(h.result);
        packet.extract(h.stack.next, 0);
        // Evaluate the out-argument before the lookahead argument.
        packet.extract(h.stack.next, (bit<32>) packet.lookahead<bit<8>>());
        transition accept;
    }
}
control I(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    apply {
        h.result.code = 255;
        if (sm.parser_error == error.PacketTooShort) { h.result.code = 1; }
        if (sm.parser_error == error.StackOutOfBounds) { h.result.code = 2; }
        sm.egress_spec = 0;
    }
}
control E(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }
control Verify(inout Headers h, inout Meta m) { apply {} }
control Update(inout Headers h, inout Meta m) { apply {} }
control D(packet_out packet, in Headers h) { apply { packet.emit(h.result); } }
V1Switch(P(), Verify(), I(), E(), Update(), D()) main;
