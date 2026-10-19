#include <core.p4>
#include <v1model.p4>

header H { bit<8> x; }
struct Headers { H first; H second; }
struct Meta {}

parser P(packet_in packet, out Headers h, inout Meta m, inout standard_metadata_t sm) {
    state start {
        packet.extract(h.first);
        h.first.x = 1;
        packet.extract(h.second);
        h.first.x = 2;
        transition accept;
    }
}
control I(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    apply { sm.egress_spec = 0; }
}
control E(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }
control Verify(inout Headers h, inout Meta m) { apply {} }
control Update(inout Headers h, inout Meta m) { apply {} }
control D(packet_out packet, in Headers h) { apply { packet.emit(h.first); } }
V1Switch(P(), Verify(), I(), E(), Update(), D()) main;
