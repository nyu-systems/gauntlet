#include <core.p4>
#include <v1model.p4>
struct H {
}
struct M {
}
parser ParserI(packet_in pk, out H hdr, inout M meta, inout standard_metadata_t smeta) {
    state start {
        transition accept;
    }
}
action drop(inout standard_metadata_t smeta_0) {
    mark_to_drop(smeta_0);
}
control IngressI(inout H hdr, inout M meta, inout standard_metadata_t smeta) {
    @name("forward") table forward {
        key = {
        }
        actions = {
            drop(smeta);
        }
        const default_action = drop(smeta);
    }
    apply {
        forward.apply();
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
