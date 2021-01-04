#include <core.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header H {
    bit<8> a;
}

header IDX {
    bit<3> idx;
}

struct Headers {
    ethernet_t eth_hdr;
    IDX idx;
    H[2] h;
}

bit<3> max(in bit<3> val, in bit<3> bound) {
    return (val < bound ? val : bound);
}

parser p(packet_in pkt, out Headers hdr) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        transition accept;
    }
}

control ingress(inout Headers h) {
    action simple_action(bool check) {
        if (check) {
            bit<3> val = max(h.idx.idx, 3w1);
            h.h[val].a = 8w1;
        }
    }
    apply {
        simple_action(true);
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

