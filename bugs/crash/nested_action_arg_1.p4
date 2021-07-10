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
    ethernet_t eth_hdr;
    H[1]  h;
}

bit<3> max(in bit<3> val, in bit<3> bound) {
    return val < bound ? val : bound;
}

parser p(packet_in pkt, out Headers hdr) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.h.next);
        transition accept;
    }
}

control ingress(inout Headers h) {
    action reset(inout H dummy) {}
    table simple_table {
        key = {}
        actions = {
            reset(h.h[max(3w1, 3w0)]);
        }
    }
    apply {
        simple_table.apply();
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

