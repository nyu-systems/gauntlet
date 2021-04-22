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
    IDX        idx;
    H[2]       h;
}

parser p(packet_in pkt, out Headers hdr) {
    state start {
        transition accept;
    }
}

control ingress(inout Headers h) {
    @name("ingress.val") bit<3> val_0;
    @name("ingress.val_1") bit<3> val_1;
    @name("ingress.bound_0") bit<3> bound_0;
    @name("ingress.hasReturned") bool hasReturned;
    @name("ingress.retval") bit<3> retval;
    @name("ingress.tmp") bit<3> tmp;
    @name("check") bool check_1;
    @name("ingress.simple_action") action simple_action() {
        check_1 = true;
        if (check_1) {
            {
                val_1 = h.idx.idx;
                bound_0 = 3w1;
                hasReturned = false;
                if (val_1 < bound_0) {
                    tmp = val_1;
                } else {
                    tmp = bound_0;
                }
                hasReturned = true;
                retval = tmp;
                val_0 = retval;
            }
            h.h[val_0].a = 8w1;
        }
    }
    apply {
        simple_action();
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

