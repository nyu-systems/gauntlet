#include <core.p4>


header H {
    bit<8>     s;
    varbit<32> v;
}

header Same {
    bit<8> same;
}

struct Headers {
    H    h;
    H[2] a;
    Same same;
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
    H[2] tmp_0;
    apply {
        h.same.setValid();
        h.same.same = 8w0;
        tmp_0[0] = h.a[0];
        tmp_0[1] = h.a[1];
        if (tmp_0 == h.a) {
            h.same.same = h.same.same | 8w8;
        }
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

