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
    ethernet_t tmp_eth_hdr;
    H tmp_h;
    ethernet_t tmp_0_eth_hdr;
    H tmp_0_h;
    ethernet_t out_h_eth_hdr;
    H out_h_h;
    ethernet_t inout_h_eth_hdr;
    H inout_h_h;
    @name("ingress.reset_action") action reset_action() {
        {
            inout_h_eth_hdr = tmp_0_eth_hdr;
            inout_h_h = tmp_0_h;
        }
        inout_h_eth_hdr.eth_type = out_h_eth_hdr.eth_type;
        {
            tmp_eth_hdr = out_h_eth_hdr;
            tmp_h = out_h_h;
        }
        {
            tmp_0_eth_hdr = inout_h_eth_hdr;
            tmp_0_h = inout_h_h;
        }
    }
    apply {
        {
            tmp_0_eth_hdr = h.eth_hdr;
            tmp_0_h = h.h;
        }
        reset_action();
        {
            h.eth_hdr = tmp_0_eth_hdr;
            h.h = tmp_0_h;
        }
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

