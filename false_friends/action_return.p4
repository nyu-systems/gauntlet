#include <core.p4>
#include <v1model.p4>

header H {
    bit<8>  a;
}

struct Headers {
    H h;
}

struct Meta {
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    bit<128> AYYzVv = 128w2;
    action LItPu(inout bit<8> val) {
        val = 8w2;
        return;
    }
    table FDnHyV {
        key = {
            AYYzVv             : exact @name("bKiScA") ;
        }
        actions = {
            LItPu(h.h.a);
        }
    }
    apply {
        FDnHyV.apply();
    }
}

parser p(packet_in b, out Headers h, inout Meta m, inout standard_metadata_t sm) {
state start {transition accept;}}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

