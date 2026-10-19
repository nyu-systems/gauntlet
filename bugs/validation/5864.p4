#include <core.p4>
#include <v1model.p4>

header H { bit<8> x; }
header_union U { H a; H b; }
struct Headers { U[1] stack; }
struct Meta {}

parser P(packet_in packet, out Headers h, inout Meta m, inout standard_metadata_t sm) {
    state start {
        packet.extract(h.stack[0].a);
        transition accept;
    }
}
control I(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    apply {
        if (h.stack[0].a.isValid()) { h.stack[0].a.x = 2; }
        sm.egress_spec = 0;
    }
}
control E(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }
control Verify(inout Headers h, inout Meta m) { apply {} }
control Update(inout Headers h, inout Meta m) { apply {} }
control D(packet_out packet, in Headers h) { apply { packet.emit(h.stack[0]); } }
V1Switch(P(), Verify(), I(), E(), Update(), D()) main;
