#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>


header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct MPSYGh {
    ethernet_t AsMA;
    ethernet_t vley;
}

header sltCAa {
    bit<128> ovLK;
    bit<32>  jPqC;
    bit<32>  LcAf;
    bit<16>  OLms;
}

struct Headers {
    ethernet_t eth_hdr;
    sltCAa     WrPW;
    sltCAa     Gmpt;
    ethernet_t UUgL;
    ethernet_t KCnV;
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
        pkt.extract(hdr.WrPW);
        pkt.extract(hdr.Gmpt);
        pkt.extract(hdr.UUgL);
        pkt.extract(hdr.KCnV);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    bool iDLUdv = !false || !!!(3w1 == 3w6);
    bool sbfmYb = true;
    bit<128> mxrokN = (!(!!!!!false || !((iDLUdv ? 3w5 : 3w4) == 3w3)) ? ~h.Gmpt.ovLK : 128w872774808);
    bool YrnseE = iDLUdv;
    action fpkgQ(out bit<128> leQc, inout bit<8> qzjk, inout bit<64> KoJi) {
        h.Gmpt.jPqC = h.Gmpt.LcAf;
        h.WrPW.OLms = h.WrPW.OLms;
        mxrokN = h.Gmpt.ovLK;
        h.UUgL.setInvalid();
        qzjk = 8w89;
        KoJi = 64w523084367;
    }
    table UDaPYW {
        key = {
            ((246w27946727 | (bit<246>)h.WrPW.OLms) |-| 246w803225113)[232:16][162:35]: exact @name("KXzejl") ;
            h.KCnV.dst_addr                                                           : exact @name("ZEPuvL") ;
            32w1137444918                                                             : exact @name("lSFiCD") ;
        }
        actions = {
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        UDaPYW.apply();
        h.WrPW.jPqC = 32w1187801485;
        h.KCnV.dst_addr = h.KCnV.src_addr;
        h.WrPW.jPqC = 32w1148684460;
        h.eth_hdr.eth_type = 16w34352;
        {
            bit<8> RfOxcc = 14;
            bit<64> picQZA = (bit<64>)h.eth_hdr.src_addr;
            fpkgQ(mxrokN, RfOxcc, picQZA);
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

