#include <tna.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

struct ingress_metadata_t {
}

struct egress_metadata_t {
}

parser SwitchIngressParser(packet_in pkt, out Headers hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        pkt.extract(ig_intr_md);
        pkt.advance(PORT_METADATA_SIZE);
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    action BnexF(out bit<64> pyri, out bit<8> ugzP, inout bit<32> FaxX) {
    }

    apply {
        ig_tm_md.ucast_egress_port = 0;
        h.eth_hdr.src_addr = 2;
        // this condition is always true
        // there is no way for the expression to be 2
        bool tmp = (h.eth_hdr.eth_type & 16w1) != 16w2;
        if (tmp) {
            h.eth_hdr.src_addr = 1;
        }
    }
}

control SwitchIngressDeparser(packet_out pkt, inout Headers h, in ingress_metadata_t ig_md, in ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md) {
    apply {
        pkt.emit(h);
    }
}

parser SwitchEgressParser(packet_in pkt, out Headers h, out egress_metadata_t eg_md, out egress_intrinsic_metadata_t eg_intr_md) {
    state start {
        pkt.extract(eg_intr_md);
        transition accept;
    }
}

control SwitchEgress(inout Headers h, inout egress_metadata_t eg_md, in egress_intrinsic_metadata_t eg_intr_md, in egress_intrinsic_metadata_from_parser_t eg_intr_md_from_prsr, inout egress_intrinsic_metadata_for_deparser_t eg_intr_dprs_md, inout egress_intrinsic_metadata_for_output_port_t eg_intr_oport_md) {
    apply {
    }
}

control SwitchEgressDeparser(packet_out pkt, inout Headers h, in egress_metadata_t eg_md, in egress_intrinsic_metadata_for_deparser_t eg_intr_dprs_md) {
    apply {
        pkt.emit(h);
    }
}

Pipeline(SwitchIngressParser(), ingress(), SwitchIngressDeparser(), SwitchEgressParser(), SwitchEgress(), SwitchEgressDeparser()) pipe;

Switch(pipe) main;

