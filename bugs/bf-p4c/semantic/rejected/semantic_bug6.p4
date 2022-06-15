#include <tna.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct NYaHlx {
    ethernet_t IihD;
    ethernet_t XNog;
    ethernet_t xzYp;
    ethernet_t mGmQ;
}

header XKkUXI {
    bit<16> GVrp;
    bit<8>  zJmW;
    bit<8>  DsAe;
}

header GDzsvG {
    bit<32> FSkE;
    bit<64> KAaz;
}

struct yrqVSV {
    ethernet_t LVeb;
    GDzsvG     kGNc;
    GDzsvG     vUip;
    GDzsvG     mTow;
}

struct qYBvyV {
    XKkUXI TniT;
}

struct DZCRJI {
    ethernet_t OKdi;
    GDzsvG     SrHm;
}

struct Headers {
    ethernet_t eth_hdr;
    GDzsvG     hWDj;
    XKkUXI     CEGx;
    XKkUXI     ptSs;
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
        pkt.extract(hdr.hWDj);
        pkt.extract(hdr.CEGx);
        pkt.extract(hdr.ptSs);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    apply {
        ig_tm_md.ucast_egress_port = 0;
        h.CEGx.GVrp = 23696;
        h.eth_hdr.src_addr = 48w1710261796;
        h.CEGx.zJmW = h.ptSs.DsAe;
        h.ptSs.zJmW = 8w2;
        h.eth_hdr.eth_type = 16w1;
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

