#include <core.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

bool simple_check() {
    return true;
}
parser p(packet_in pkt, out Headers hdr) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        transition accept;
    }
}

action assign(inout bit<16> eth_t, inout bit<48> target_addr, bool check_bool) {
    if (check_bool) {
        if (simple_check() && 0xDEAD != eth_t) {
            target_addr = 48w1;
        }
    }
}
control ingress(inout Headers h) {
    apply {
        assign(h.eth_hdr.eth_type, h.eth_hdr.dst_addr, true);
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

