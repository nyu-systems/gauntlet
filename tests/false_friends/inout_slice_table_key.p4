#include <core.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

parser p(packet_in pkt, out Headers hdr) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        transition accept;
    }
}

control ingress(inout Headers h) {
    bit<8> tmp_val = 1;
    action simple_action(inout bit<4> dummy) {
    }
    table simple_table {
        key = {
            tmp_val : exact @name("dummy") ;
        }
        actions = {
            NoAction();
        }
    }
    apply {
        simple_action(tmp_val[7:4]);
        if (simple_table.apply().hit) {
            h.eth_hdr.eth_type = 1;
        }
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

