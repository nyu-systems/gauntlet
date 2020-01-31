#include <core.p4>
#include <v1model.p4>

header H {
    bit<4> a;
    int<4>  b;
    bit<4>  c;
    int<4>  d;
    bit<4>  e;
}

struct Headers {
    H    h;
}

struct Meta {
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    apply {
        bit<4> tmp = 4w0 - 4w1;
        h.h.a = tmp / 4w2;
        h.h.b = 4s7 >> 1 >> 1;
        h.h.c = 4w15 >> 1 >> 1;
        h.h.d = -4s7 >> 1 >> 1;
        h.h.e = tmp >> 1 >> 1;
    }
}

parser p(packet_in b, out Headers h, inout Meta m, inout standard_metadata_t sm) {
state start {transition accept;}}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

