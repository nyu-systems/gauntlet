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
    H          a;
}

parser p(packet_in pkt, out Headers hdr) {
    state start {
        transition accept;
    }
}

control ingress(inout Headers h) {
    @name("ingress.tmp") Headers tmp_0;
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    Headers dummy;
    @name("ingress.reset") action reset() {
        {
            tmp_0.eth_hdr = dummy.eth_hdr;
            tmp_0.a = dummy.a;
        }
    }
    bit<64> key_0;
    @name("ingress.tbl1") table tbl1_0 {
        key = {
            key_0: exact @name("test") ;
        }
        actions = {
            reset();
            @defaultonly NoAction_0();
        }
        default_action = NoAction_0();
    }
    apply {
        tmp_0.eth_hdr.setValid();
        tmp_0.a.setValid();
        {
            {
                tmp_0.eth_hdr.dst_addr = 48w1;
                tmp_0.eth_hdr.src_addr = 48w1;
                tmp_0.eth_hdr.eth_type = 16w1;
            }
            {
                tmp_0.a.a = 8w1;
            }
        }
        {
            key_0 = 64w1;
            switch (tbl1_0.apply().action_run) {
                reset: {
                }
                default: {
                }
            }

        }
        h.eth_hdr.eth_type = tmp_0.eth_hdr.eth_type;
        h.eth_hdr.eth_type[1:0] = 2w1;
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

