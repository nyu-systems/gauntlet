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
    H[2]     h;
}

extern bit<64> dummy(out H val);

parser p(packet_in pkt, out Headers hdr) {
    bool dummy_bool = 64w2 == dummy(hdr.h[(64w2 == dummy(hdr.h[3w0]) ? hdr.eth_hdr.eth_type : 16w1)]);
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.h.next);
        pkt.extract(hdr.h.next);
        transition accept;
    }
}

control ingress(inout Headers h) {
    apply {
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

