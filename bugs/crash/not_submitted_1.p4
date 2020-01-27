#include <core.p4>
#include <v1model.p4>

header H {
    bit<64> a;
    bit<8>  b;
}


struct Headers {
    H    h;
}

struct Meta {
}

bit<8> do_thing() {
    H tmp_var = { 64w0, 8w0 };
    tmp_var = tmp_var;
    if (tmp_var.b >= 4) {
    } else {
        if (tmp_var.a >= 1 ) {
            tmp_var = tmp_var;
        }
        if (tmp_var.a != 1) {
            tmp_var = tmp_var;
        }
    }
    return 8w3;
}
control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    action do_action() {
        h.h.b = do_thing();
    }

    apply {
        do_action();
        do_thing();


    }
}

parser p(packet_in b, out Headers h, inout Meta m, inout standard_metadata_t sm) {
state start {transition accept;}}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

