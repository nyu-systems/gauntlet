#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>


header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header zuRjuM {
    bit<32> dvyL;
    bit<64> DBgh;
    bit<8>  bGgN;
    bit<8>  AwNE;
}

header gXlPSy {
    bit<64> vVci;
    bit<16> lPST;
}

struct WdALYL {
    zuRjuM wYsZ;
    gXlPSy YxdQ;
    gXlPSy DumY;
}

header UPkFeC {
    bit<16> ZWXC;
    bit<64> CJWy;
    bit<16> YBrx;
    bit<32> MKea;
}

struct Headers {
    ethernet_t eth_hdr;
    ethernet_t ZpbE;
    ethernet_t EFqD;
    ethernet_t oNmx;
    UPkFeC     NGDN;
}

struct ingress_metadata_t {
}

struct egress_metadata_t {
}

action KpGyb() {
    bit<128> mpunGx = 128w1993327285;
    mpunGx = (!!false ? 128w1379783245 : 128w1029331452 - mpunGx & 136w649435181[130:3]);
    {
        mpunGx = 128w1496550169;
        if (!!false) {
            if (true) {
                mpunGx = ~((128w505276397 & 128w1110456913) << (bit<8>)128w1390484747) ^ 128w1846117805;
            } else {
                mpunGx = mpunGx;
            }
        } else {
            mpunGx = mpunGx;
        }
        mpunGx = 128w1059619807;
        mpunGx = 128w969870816;
        mpunGx = mpunGx;
        mpunGx = 128w501153802;
        return;
        mpunGx = 128w1011351893 / 128w1750442460;
    }
    mpunGx = mpunGx | 128w2057453047;
}
parser SwitchIngressParser(packet_in pkt, out Headers hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        pkt.extract(ig_intr_md);
        pkt.advance(PORT_METADATA_SIZE);
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.ZpbE);
        pkt.extract(hdr.EFqD);
        pkt.extract(hdr.oNmx);
        pkt.extract(hdr.NGDN);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    bool CeBtiu = true;
    action GtpUl() {
        h.EFqD.src_addr = 48w1278853432;
        h.EFqD.eth_type = ((bit<93>)h.NGDN.CJWy != ~93w352803268 ? 90w988560678 : 90w2116148357)[59:4][47:32];
        h.NGDN.MKea = 32w1405119058 % 32w1710938566;
        return;
        h.eth_hdr.eth_type = 32236;
        bit<16> CnqYcK = h.NGDN.YBrx;
        h.NGDN.CJWy = 64w196941333;
        h.NGDN.CJWy = ((bit<125>)h.NGDN.MKea)[85:22] |+| h.NGDN.CJWy;
        bool DaYQNJ = true;
        return;
    }
    action XQjHv(inout bit<8> xTbI, in bit<8> caeT) {
        h.oNmx.src_addr = h.eth_hdr.dst_addr;
        bit<32> ELdSwl = 32w969744753;
        h.NGDN.CJWy = 109w1766318147[85:22];
        return;
        h.NGDN.CJWy = 738243047;
        h.NGDN.CJWy = ((bit<177>)h.EFqD.src_addr)[104:41];
        ELdSwl = (bit<21>)704644 ++ 11w1207;
        xTbI = 8w228 * 8w137 |+| (bit<8>)126 & 8w49;
        bit<16> TWCwRf = 16w29528;
    }
    table zfVwSh {
        key = {
            48w717466887: exact @name("ubHGDG") ;
        }
        actions = {
            GtpUl();
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        h.NGDN.ZWXC = 16w2700 |+| ((27w9006884 ^ 27w101126812) * (bit<27>)h.NGDN.CJWy)[17:2];
        h.oNmx.src_addr = h.ZpbE.src_addr;
        zfVwSh.apply();
        h.NGDN.CJWy = 64w1632951142;
        h.EFqD.dst_addr = 48w1233204189;
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

