#include <core.p4>
#include <v1model.p4>

header H {
    bit<16>  a;
    bit<16>  b;
}

struct Headers {
    H    h;
}

struct Meta {
}


parser p(packet_in pkt, out Headers hdr, inout Meta m, inout standard_metadata_t sm) {
    state start {
        transition accept;
    }
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {

    action simple_action() {
        sm.egress_spec = 9w0;
    }

    table simple_table {
        key = {
            h.h.b: exact @name("CCctuD") ;
        }
        actions = {
            NoAction;
            simple_action;
        }
    }

    apply {
        switch (simple_table.apply().action_run) {
            simple_action: {
                return;
            }
        }
        h.h.a = 16w0;
    }
}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

