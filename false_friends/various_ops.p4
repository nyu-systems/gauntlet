#include <core.p4>
#include <v1model.p4>

header OVERFLOW {
    bit<8> a;
    bit<8> b;
}

header UNDERFLOW {
    bit<8> a;
    bit<8> b;
}

header MOD {
    bit<4> a;
    bit<4> b;
    bit<4> c;
    bit<4> d;
}

header RSH {
    bit<4> a;
    int<4>  b;
    bit<4>  c;
    int<4>  d;
    bit<4>  e;
    bit<4>  g;
}

header LSH {
    bit<8> a;
    bit<8> b;
}

header COMPARE {
    bit<8> a;
    bit<8> b;
    bit<8> c;
}

struct Headers {
    OVERFLOW overflow;
    UNDERFLOW underflow;
    RSH rshift;
    LSH lshift;
    MOD mod;
    COMPARE comp;
}

struct Meta {}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    apply {
        //overflow
        h.overflow.a = 8w255 |+| 8w2;
        h.overflow.b = 8w3 |+| 8w0;
        //underflow
        h.underflow.a = 8w1 |-| 8w2;
        h.underflow.a = 8w3 |-| 8w0;
        // unsigned mod
        h.mod.a = 4w1 % 4w8;
        // signed mod
        h.mod.b = 1 % 4w8;
        h.mod.c = 3 % 2;

        // right shift
        bit<4> tmp = 4w0 - 4w1;
        h.rshift.a = tmp / 4w2;
        h.rshift.b = 4s7 >> 1 >> 1;
        h.rshift.c = 4w15 >> 1 >> 1;
        h.rshift.d = -4s7 >> 1 >> 1;
        h.rshift.e = tmp >> 1 >> 1;
        h.rshift.g = 4w1 >> 8w16;
        //left shift
        h.lshift.a = (bit<8>)(4w4 << 8w2);
        h.lshift.b = (bit<8>)(4w4 << 8w16);
        // comparing various unsigned constants
        // if (4w15  > 2) { h.comp.a = 1; }
        // if (4w3  > 2) { h.comp.b = 1; }
        // if (-1  > 4w2) { h.comp.c = 1; }
    }
}

parser p(packet_in b, out Headers h, inout Meta m, inout standard_metadata_t sm) {
state start {transition accept;}}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

