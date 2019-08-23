#include <core.p4>
#include <v1model.p4>
header Ethernet {
    bit<48> src;
    bit<48> dest;
    bit<16> tst;
}
struct Headers {
    Ethernet eth;
}
parser prs(packet_in p, out Headers h) {
    state start {
        transition accept;
    }
}
control c(inout Headers h, inout standard_metadata_t sm) {
    @name(".NoAction") action NoAction_1() {
    }
    @name("do_act") action do_act_0() {
    }
    @name("tns") table tns {
        key = {
            h.eth.tst[13:4]: exact @name("h.eth.tst[13:4]") ;
        }
        actions = {
            do_act_0();
            @defaultonly NoAction_1();
        }
        default_action = NoAction_1();
    }
    apply {
        tns.apply();
    }
}
parser p<H>(packet_in _p, out H h);
control ctr<H, SM>(inout H h, inout SM sm);
package top<H, SM>(p<H> _p, ctr<H, SM> _c);
top<Headers, standard_metadata_t>(prs(), c()) main;
