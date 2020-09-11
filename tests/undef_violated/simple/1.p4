#include <core.p4>

header H {
    bit<8> a;
}

struct Headers {
    H h;
}

struct Meta {
}

parser p(packet_in pkt, out Headers hdr) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.h);
        transition accept;
    }
}

control ingress(inout Headers h) {
    apply {
        h.h.setValid();
        // this is undefined
        bit<8> tmp;
        // h.h.b's output will be undefined
        h.h.a = tmp + 1;
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;
