#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>


struct ingress_metadata_t {}
struct egress_metadata_t {}

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header XjtyJt {
    bit<16> jyGI;
}

header ayvIAs {
    bit<32> qOqL;
    bit<16> zdta;
    bit<16> ofGQ;
}

struct QnnfFa {
    bit<32> itYJ;
    ayvIAs  lkIk;
}

struct qRPIMQ {
    ethernet_t hMDC;
    bit<32>    pkYr;
}

struct Headers {
    ethernet_t eth_hdr;
    ethernet_t rLCD;
    XjtyJt     IQDz;
    ayvIAs     jtKm;
}

struct Meta {
}

parser SwitchIngressParser(packet_in pkt, out Headers hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        pkt.extract(ig_intr_md);
        pkt.advance(PORT_METADATA_SIZE);
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.rLCD);
        pkt.extract(hdr.IQDz);
        pkt.extract(hdr.jtKm);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t m, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    egress_intrinsic_metadata_from_parser_t IMTqZc;
    QnnfFa GMIVAR = { ((((!true) ? (bit<32>)(h.IQDz.jyGI) : (bit<32>)(h.jtKm.qOqL))) ^ (32w70227964 - 32w1395179268)), { (~32w593811866), (bit<16>)(h.eth_hdr.dst_addr), 16w34237 } };
    egress_intrinsic_metadata_for_deparser_t JShErk;
    action aJDhe() {
        GMIVAR.lkIk.zdta = 16w30062;
        h.jtKm.qOqL = 32w1111256358;
        h.jtKm.qOqL = (bit<32>)(h.rLCD.eth_type);
        h.IQDz.jyGI = (bit<16>)(GMIVAR.lkIk.qOqL);
        GMIVAR.lkIk.zdta = (bit<16>)(h.rLCD.eth_type);
    }
    action ZxJIB() {
        {
            h.rLCD.eth_type = ((15w23135 ++ (bit<1>)(GMIVAR.itYJ)) | 16w64581);
            QnnfFa CdVAOF = { 32w1796825964, { ((bit<32>)(h.eth_hdr.dst_addr) + 32w1445461796), (bit<16>)(h.jtKm.qOqL), (16w64705 | (((16w48430 | (bit<16>)(GMIVAR.itYJ))) - 16w32060)) } };
            h.eth_hdr.src_addr = 48w1409641576;
            h.eth_hdr.dst_addr = 48w113553140;
            bit<64> dqwpzO = ((bit<64>)(h.jtKm.ofGQ) & (((64w714233827 % 64w930299546) | 64w734553286)));
            h.rLCD.dst_addr = 48w772623894;
            return;
        }
        h.rLCD.eth_type = ((bit<16>)(h.eth_hdr.dst_addr) & 16w9664);
        h.eth_hdr.src_addr = 48w4404504;
        GMIVAR.itYJ = (32w677752971 / 32w1736429860);
    }
    table dQErnP {
        key = {
            (((bit<124>)(h.jtKm.qOqL))[71:40]): exact @name("QiZTPN") ;
            48w1067335803                     : exact @name("Qkuhgu") ;
            16w61779                          : exact @name("LJdiwc") ;
        }
        actions = {
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        ZxJIB();
        h.rLCD.dst_addr = 48w210744633;
        h.rLCD.dst_addr = (48w1418459394 - 48w1434135308);
        GMIVAR.itYJ = 32w1312564181;
        h.rLCD.src_addr = 48w509973521;
        ingress_intrinsic_metadata_for_deparser_t KDxEOL;
        bit<16> qzYgFy = 16w39983;
    }
}


// ---------------------------------------------------------------------------
// Ingress Deparser
// ---------------------------------------------------------------------------
control SwitchIngressDeparser(
        packet_out pkt,
        inout Headers hdr,
        in ingress_metadata_t ig_md,
        in ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md) {

    apply {
        pkt.emit(hdr);
    }

}
parser SwitchEgressParser(
        packet_in pkt,
        out Headers hdr,
        out egress_metadata_t eg_md,
        out egress_intrinsic_metadata_t eg_intr_md) {
    state start {
        pkt.extract(eg_intr_md);
        transition accept;
    }
}

control SwitchEgressDeparser(
        packet_out pkt,
        inout Headers hdr,
        in egress_metadata_t eg_md,
        in egress_intrinsic_metadata_for_deparser_t eg_intr_dprs_md) {

    apply {
        pkt.emit(hdr);
    }
}

control SwitchEgress(
        inout Headers hdr,
        inout egress_metadata_t eg_md,
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
