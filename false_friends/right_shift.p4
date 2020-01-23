#include <core.p4>
#include <v1model.p4>

header H {
    bit<128> a;
    bit<32>  b;
}

struct Headers {
    H    h;
}

struct Meta {
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    apply {
        bit<32> tmp = 32w0 - 32w1;
        h.h.b = tmp / 32w2;
    }
}

parser p(packet_in b, out Headers h, inout Meta m, inout standard_metadata_t sm) {
state start {transition accept;}}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

