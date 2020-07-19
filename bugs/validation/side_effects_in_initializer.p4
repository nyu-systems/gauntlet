#include <core.p4>
header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}


header H {
    bit<16> a;
}

struct Headers {
    ethernet_t eth_hdr;
}

bit<48> set(inout bit<48> set) {
    set = 1;
    return 48w2;
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
    Headers tmp = { { h.eth_hdr.dst_addr, set(h.eth_hdr.dst_addr), 1 } };

    apply {
        h.eth_hdr.dst_addr = tmp.eth_hdr.dst_addr;
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

