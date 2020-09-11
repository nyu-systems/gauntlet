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
    H          h;
}

parser p(packet_in pkt, out Headers hdr) {
    state start {
        pkt.extract<ethernet_t>(hdr.eth_hdr);
        pkt.extract<H>(hdr.h);
        transition accept;
    }
}

control ingress(inout Headers h) {
    Headers tmp;
    Headers tmp_0;
    Headers out_h;
    Headers inout_h;
    @name("ingress.reset_action") action reset_action() {
        {
            inout_h.eth_hdr = tmp_0.eth_hdr;
            inout_h.h = tmp_0.h;
        }
        inout_h.eth_hdr.eth_type = out_h.eth_hdr.eth_type;
        {
            tmp.eth_hdr = out_h.eth_hdr;
            tmp.h = out_h.h;
        }
        {
            tmp_0.eth_hdr = inout_h.eth_hdr;
            tmp_0.h = inout_h.h;
        }
    }
    apply {
        {
            tmp_0.eth_hdr = h.eth_hdr;
            tmp_0.h = h.h;
        }
        reset_action();
        {
            h.eth_hdr = tmp_0.eth_hdr;
            h.h = tmp_0.h;
        }
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

