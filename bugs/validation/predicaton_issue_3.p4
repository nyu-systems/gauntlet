#include <core.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header H {
    bit<8> a;
}

struct Headers {
    ethernet_t    eth_hdr;
    H[2] h;
}

parser p(packet_in pkt, out Headers hdr) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        transition accept;
    }
}

bit<3> max(in bit<3> val, in bit<3> bound) {
    return (val < bound ? val : bound);
}

control ingress(inout Headers h) {
    bool bool_val = true;
    action perform_action() {
        if (bool_val) {
            h.h[max(3w0, 3w1)].a = 1;
        }
    }
    apply {
        perform_action();
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

