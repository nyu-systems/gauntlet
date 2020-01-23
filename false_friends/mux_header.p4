#include <core.p4>
#include <v1model.p4>

header H {
    bit<32> a;
}


struct Headers {
    H h;
}

struct Meta {
}

bit<32> TJRRFYE() {
    H[2] EpaeHp;
    H[2] DkBlyx;

    if (DkBlyx[0].a <= 3) {
        EpaeHp[0] = DkBlyx[1];
        DkBlyx[1] = EpaeHp[1];
    }
    return EpaeHp[0].a;
}
control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    action ikKPp() {
        h.h.a = (bit<32>)(TJRRFYE());

    }
    table ldAxlM {
        key = {
            sm.egress_spec        : exact @name("nRNQnO") ;
        }
        actions = {
            ikKPp();
        }
    }
    apply {
        ldAxlM.apply();
    }
}

parser p(packet_in b, out Headers h, inout Meta m, inout standard_metadata_t sm) {
state start {transition accept;}}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

