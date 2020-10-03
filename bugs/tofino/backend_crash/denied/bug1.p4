#include <core.p4>
#include <tna.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

struct Meta {
}

bit<32> return_one() {
    return 1;
}
control ingress(inout Headers h, inout Meta m, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    apply {
        h.eth_hdr.eth_type = (bit<16>)return_one();
    }
}

parser SwitchIngressParser(
packet_in pkt,
out Headers hdr,
out Meta ig_md,
out ingress_intrinsic_metadata_t ig_intr_md) {
state start {
pkt.extract(ig_intr_md);
transition select(ig_intr_md.resubmit_flag) {
1 : parse_resubmit;
0 : parse_port_metadata;
}
}
state parse_resubmit {
transition reject;
}
state parse_port_metadata {
pkt.advance(PORT_METADATA_SIZE);
transition accept;
}
}
control SwitchIngressDeparser(
packet_out pkt,
inout Headers hdr,
in Meta ig_md,
in ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md) {
apply {
}
}
parser SwitchEgressParser(
packet_in pkt,
out Headers hdr,
out Meta eg_md,
out egress_intrinsic_metadata_t eg_intr_md) {
state start {
pkt.extract(eg_intr_md);
transition accept;
}
}
control SwitchEgressDeparser(
packet_out pkt,
inout Headers hdr,
in Meta eg_md,
in egress_intrinsic_metadata_for_deparser_t eg_intr_dprs_md) {
apply {
}
}
control SwitchEgress(
inout Headers hdr,
inout Meta eg_md,
in egress_intrinsic_metadata_t eg_intr_md,
in egress_intrinsic_metadata_from_parser_t eg_intr_md_from_prsr,
inout egress_intrinsic_metadata_for_deparser_t eg_intr_dprs_md,
inout egress_intrinsic_metadata_for_output_port_t eg_intr_oport_md) {
apply {}
}
Pipeline(SwitchIngressParser(),
ingress(),
SwitchIngressDeparser(),
SwitchEgressParser(),
SwitchEgress(),
SwitchEgressDeparser()) pipe;

Switch(pipe) main;
