#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header H {
    bit<8>  a;
}

struct Headers {
    ethernet_t eth_hdr;
    H     h;
}

struct Meta {
}

bit<8> barrier_function(out bit<8> val) {
    val = 8w139;
    return val;
}
parser p(packet_in pkt, out Headers hdr, inout Meta m, inout standard_metadata_t sm) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.h);
        transition accept;
    }
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    action simple_action() {
        h.eth_hdr.eth_type = 1;
    }
    table simple_table {
        key = {
            48w1: exact @name("key") ;
        }
        actions = {
            simple_action();
        }
    }
    apply {
        h.eth_hdr.src_addr = (bit<48>)barrier_function(h.h.a);
        switch (simple_table.apply().action_run) {
            simple_action: {
                return;
            }
        }
        h.eth_hdr.eth_type = 2;

    }
}

control vrfy(inout Headers h, inout Meta m) {
    apply {
    }
}

control update(inout Headers h, inout Meta m) {
    apply {
    }
}

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    apply {
    }
}

control deparser(packet_out pkt, in Headers h) {
    apply {
        pkt.emit(h);
    }
}

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

