#include <core.p4>
#include <v1model.p4>
struct H {
}
struct M {
    bit<32> hash1;
}
parser ParserI(packet_in pk, out H hdr, inout M meta, inout standard_metadata_t smeta) {
    state start {
        transition accept;
    }
}
control IngressI(inout H hdr, inout M meta, inout standard_metadata_t smeta) {
    @name(".NoAction") action NoAction_1() {
    }
    @name(".NoAction") action NoAction_2() {
    }
    @name("drop") action drop_0() {
        mark_to_drop(smeta);
    }
    @name("drop") action drop_1() {
        mark_to_drop(smeta);
    }
    @name("indirect") table indirect {
        key = {
        }
        actions = {
            drop_0();
            NoAction_1();
        }
        const default_action = NoAction_1();
        @name("ap") @max_group_size(200) implementation = action_profile(32w128);
    }
    @name("indirect_ws") table indirect_ws {
        key = {
            meta.hash1: selector @name("meta.hash1") ;
        }
        actions = {
            drop_1();
            NoAction_2();
        }
        const default_action = NoAction_2();
        @name("ap_ws") @max_group_size(200) implementation = action_selector(HashAlgorithm.identity, 32w1024, 32w10);
    }
    apply {
        indirect.apply();
        indirect_ws.apply();
    }
}
control EgressI(inout H hdr, inout M meta, inout standard_metadata_t smeta) {
    apply {
    }
}
control DeparserI(packet_out pk, in H hdr) {
    apply {
    }
}
control VerifyChecksumI(inout H hdr, inout M meta) {
    apply {
    }
}
control ComputeChecksumI(inout H hdr, inout M meta) {
    apply {
    }
}
V1Switch<H, M>(ParserI(), VerifyChecksumI(), IngressI(), EgressI(), ComputeChecksumI(), DeparserI()) main;
