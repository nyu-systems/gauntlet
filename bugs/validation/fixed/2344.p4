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

bit<32> simple_function() {
    H tmp1;
    if (!tmp1.isValid()) {
        tmp1.setValid();
        tmp1.a = 10;
    } else {
        tmp1.a = tmp1.a + 15;
    }
    return tmp1.a;
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    action simple_action() {
        h.h.a = simple_function();
    }
    table simple_table {
        key = {
        }
        actions = {
            simple_action();
        }
        default_action = simple_action;
    }
    apply {
        simple_table.apply();
        simple_table.apply();
    }
}

parser p(packet_in b, out Headers h, inout Meta m, inout standard_metadata_t sm) {
state start {transition accept;}}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

