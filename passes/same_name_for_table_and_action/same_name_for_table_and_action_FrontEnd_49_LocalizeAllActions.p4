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
    @name("do_something") action do_something_1() {
        mark_to_drop(smeta);
    }
    @name("do_something") table do_something_0 {
        key = {
            smeta.ingress_port: exact @name("smeta.ingress_port") ;
        }
        actions = {
            do_something_1();
            NoAction_1();
        }
        const default_action = NoAction_1();
    }
    apply {
        do_something_0.apply();
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
