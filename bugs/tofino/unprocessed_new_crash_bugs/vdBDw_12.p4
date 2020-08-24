#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header hwXCMl {
    bit<16>  kayJ;
    bit<4>   uPYB;
    bit<64>  boMx;
    bit<32>  HssD;
    bit<128> bpqE;
    bit<4>   padding;
}

header aLZTkt {
    bit<128> KgzY;
    bit<4>   KKMt;
    bit<8>   naXO;
    bit<16>  GLgi;
    bit<4>   padding;
}

header kkkmlU {
    bit<8>   AkEk;
    bit<32>  uHyV;
    bit<8>   qfJW;
    bit<128> JvKt;
    bit<128> ekTX;
}

struct Headers {
    ethernet_t eth_hdr;
    ethernet_t NEFF;
    aLZTkt     ZTTK;
    kkkmlU     iKSj;
    kkkmlU     gMFt;
    aLZTkt     yJgr;
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
        pkt.extract(hdr.NEFF);
        pkt.extract(hdr.ZTTK);
        pkt.extract(hdr.iKSj);
        pkt.extract(hdr.gMFt);
        pkt.extract(hdr.yJgr);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    bool ZgZhpG = 121w1580762314510334646302988925858970590 != 522846651 % 2147188233 ^ -(1755479280 + -304518732) || !true || (true || true);
    bit<64> dZMtKM = (bit<64>)-1570801587 |-| (bit<64>)64w2223287503789029197;
    bit<128> DMclPI = 128w240772279537856106243732202701425982279;
    bit<8> rdhoPm = 14w13762[12:5];
    bit<8> GuWvBI = h.yJgr.naXO << h.iKSj.AkEk;
    bool JquKHe = !ZgZhpG;
    action vAhBb(bit<8> RHWX) {
        h.gMFt.qfJW = (bit<8>)(8w250 + ((ZgZhpG ? 8w198 : rdhoPm) >> 8w11));
        h.NEFF.dst_addr = h.eth_hdr.src_addr;
        h.gMFt.uHyV = h.iKSj.uHyV;
        dZMtKM = dZMtKM;
        dZMtKM = dZMtKM;
        h.ZTTK.KKMt = h.ZTTK.padding;
        dZMtKM[49:2] = h.NEFF.dst_addr;
    }
    table ruiVIV {
        key = {
        }
        actions = {
            vAhBb();
        }
    }
    table qkvGfg {
        key = {
            64w13573831872230119073               : exact @name("dqMhgr") ;
            91w2187822960403870164469547752[49:46]: exact @name("IsVmta") ;
        }
        actions = {
            vAhBb();
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        h.yJgr.padding = 99w85631470308768458393210691477[16:13];
        dZMtKM = 64w10000228274855258023 ^ 64w17471261283326488564;
        h.iKSj.JvKt = 1555370092 % 1884148113 - (bit<128>)128w254971987166132818612584748922583842905 ^ h.yJgr.KgzY;
        h.iKSj.qfJW = 8w24;
        bit<8> MAsodh = 8w65;
        ruiVIV.apply();
        h.ZTTK.GLgi = 16w29850;
        h.gMFt.AkEk = 8w54;
        h.ZTTK.padding = h.ZTTK.padding;
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

