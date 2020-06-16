#include <core.p4>
header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}


bit<48> simple_val_fun() {
    ethernet_t tmp = { 1, 1, 1 };
    tmp.src_addr = 2;
    return tmp.src_addr;
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

    action dummy_action() {
        if(h.eth_hdr.eth_type == 1) {
            h.eth_hdr.src_addr = 1;
        } else {
            h.eth_hdr.src_addr = simple_val_fun();
        }
    }

    apply {
        dummy_action();
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

