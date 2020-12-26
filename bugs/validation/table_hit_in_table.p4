#include <core.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
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
    action assign_eth() {
        h.eth_hdr.eth_type = 16w1;
    }
    table tbl1 {
        key = {
            32w10: exact @name("pOpzaJ") ;
        }
        actions = {
            assign_eth();
        }
        default_action = assign_eth();
    }
    table tbl2 {
        key = {
            (tbl1.apply().hit ? h.eth_hdr.src_addr : h.eth_hdr.dst_addr): exact @name("key") ;
        }
        actions = {
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    apply {
        switch (tbl2.apply().action_run) {
        }
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

