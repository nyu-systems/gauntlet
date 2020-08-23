#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>


header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header gOEXzg {
    bit<8>   jfMW;
    bit<16>  cXDK;
    bit<128> XzCJ;
    bit<8>   mRRd;
}

struct Headers {
    ethernet_t eth_hdr;
    gOEXzg     ghlH;
    ethernet_t sqUg;
}

struct ingress_metadata_t {
}

struct egress_metadata_t {
}

action ksanC(inout bit<8> LaIp) {
    bool qRDIuR = false;
    return;
    LaIp = 8w113;
    LaIp = LaIp;
    LaIp = LaIp;
    LaIp = 8w114 |+| 8w222 % 8w115;
}
parser SwitchIngressParser(packet_in pkt, out Headers hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        pkt.extract(ig_intr_md);
        pkt.advance(PORT_METADATA_SIZE);
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.ghlH);
        pkt.extract(hdr.sqUg);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    bool fphHPA = !(!!(false && 65w476143142 == 1713434667) && !!false);
    egress_intrinsic_metadata_t yNzQkQ;
    bool nxuCWN = fphHPA;
    bit<32> pWDZds = 32w1093003139;
    action HkBre(inout bit<8> rdaS) {
        pWDZds = pWDZds ^ (32w195112947 | 32w304186669 ^ 32w1700627458 |-| 32w798231860);
        rdaS = 8w214;
        {
            h.sqUg.src_addr = 48w1506436257;
            pWDZds = pWDZds;
            ksanC(h.ghlH.mRRd);
            pWDZds = 32w822539313;
            rdaS = 8w38;
            h.sqUg.src_addr = 48w722358375;
            h.ghlH.jfMW = 42;
            pWDZds = 32w998661076;
            h.ghlH.jfMW = 95w666898257[54:47];
        }
        h.sqUg.src_addr = (74w2080360671 / 74w185170042)[66:19];
        bool LNDeUp = 102w579859452 == 102w1907393713;
        h.ghlH.mRRd = 8w44;
        if ((bit<116>)pWDZds == ((bit<147>)318283927)[121:6] + (bit<116>)pWDZds) {
            h.ghlH.XzCJ = -h.ghlH.XzCJ;
        } else {
            ksanC(h.ghlH.mRRd);
        }
    }
    action IKdad() {
        h.ghlH.cXDK = 16w14327;
        {
            pWDZds = pWDZds |+| pWDZds |-| ((bit<23>)(5708810 & 23w4045595) ++ 9w348);
            h.ghlH.jfMW = h.ghlH.jfMW;
            pWDZds = ((bit<141>)h.sqUg.eth_type)[90:59];
            h.ghlH.XzCJ = 128w1009573043;
            h.sqUg.eth_type = 16w10128;
        }
        bool KgFZQz = !!nxuCWN;
        h.eth_hdr.eth_type = 16w23010;
        h.eth_hdr.src_addr = 48w937129453 / 48w1655361945;
        h.eth_hdr.src_addr = 48w1212692201;
        return;
    }
    table WZHqAS {
        key = {
            h.ghlH.XzCJ + 128w926505922: exact @name("szLrur") ;
            128w410138288              : exact @name("bPvNXc") ;
            128w1128276615             : exact @name("DWdNWk") ;
        }
        actions = {
            HkBre(h.ghlH.jfMW);
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        bit<128> XmAKQD = h.ghlH.XzCJ;
        h.sqUg.src_addr = 23532838;
        h.eth_hdr.eth_type = h.sqUg.eth_type;
        if (43w759814988 != 43w1805247570) {
            h.sqUg.eth_type = h.sqUg.eth_type | 16w33431;
        } else {
            h.sqUg.dst_addr = ~48w282994217 + 826886573;
        }
        h.ghlH.mRRd = 8w189 & ((bit<17>)h.eth_hdr.eth_type * 17w96862)[15:8];
        h.ghlH.XzCJ = h.ghlH.XzCJ;
        return;
        XmAKQD = 128w1803311763;
        WZHqAS.apply();
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

