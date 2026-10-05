#include <core.p4>
#include <v1model.p4>

header Result { bit<8> error_code; }
header H { bit<8> again; }
struct Headers { Result result; H[1] stack; }
struct Meta {}

parser P(packet_in packet, out Headers h, inout Meta m,
              inout standard_metadata_t sm) {
    int<32> index;
    state start {
        packet.extract(h.result);
        index = 0;
        transition parse_element;
    }
    state parse_element {
        packet.extract(h.stack[index]);
        index += 1;
        transition select(h.stack[index - 1].again) {
            0: parse_element;
            default: accept;
        }
    }
}
control I(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    apply {
        h.result.error_code = 255;
        if (sm.parser_error == error.NoError) { h.result.error_code = 0; }
        if (sm.parser_error == error.PacketTooShort) { h.result.error_code = 1; }
        if (sm.parser_error == error.StackOutOfBounds) { h.result.error_code = 2; }
        sm.egress_spec = 0;
    }
}
control E(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }
control Verify(inout Headers h, inout Meta m) { apply {} }
control Update(inout Headers h, inout Meta m) { apply {} }
control D(packet_out packet, in Headers h) { apply { packet.emit(h.result); } }
V1Switch(P(), Verify(), I(), E(), Update(), D()) main;
