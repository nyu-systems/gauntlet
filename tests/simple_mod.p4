#include <core.p4>


header H {
    bit<32>  a;
    bit<32>  b;
}

struct Headers {
    H     h;
    H     h1;
}

parser p(packet_in pkt, out Headers hdr) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        transition accept;
    }
}

bit<32> simple_fun(inout bit<32> val) {
    if (val == 32w1) {
        val = 2;
        return 21;
    } else {
        val = 3;
    }
    return 32w2;
}

control ingress(inout Headers h) {

    apply {
        h.h.b = simple_fun(h.h.a);
        h.h1.setInvalid();
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

