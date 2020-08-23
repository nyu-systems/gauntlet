#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>


header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct pvfuuJ {
    ethernet_t qonP;
    ethernet_t ofWC;
    ethernet_t Srvq;
    ethernet_t xSrk;
    ethernet_t gasw;
}

header QbmKNc {
    bit<16> BrQd;
}

struct biuuBp {
    ethernet_t WOeq;
    ethernet_t tWAO;
}

struct QeWeoL {
    QbmKNc     RMai;
    ethernet_t FGVP;
    QbmKNc     PtRD;
    ethernet_t IJFG;
    QbmKNc     DjQy;
}

header WwFLHn {
    bit<8>  vNOp;
    bit<64> KmYB;
    bit<64> EXyN;
}

struct Headers {
    ethernet_t eth_hdr;
    WwFLHn     IPIG;
    QbmKNc     GCXt;
}

struct ingress_metadata_t {
}

struct egress_metadata_t {
}

action ygcMV(in bit<64> Jfmh, out bit<32> MQZB, inout bit<16> dxdL) {
    MQZB = 32w296102226 >> (bit<8>)(!(557157310 * 128w1207623827 == (bit<128>)MQZB) ? (bit<32>)32w1642702106 : 32w263776836);
    MQZB = MQZB;
    bool UOFIGf = 32w1870666837 == 32w1431134851 && !!(false || !!false || !false);
    bool TerIWU = UOFIGf;
    MQZB = 32w170383287;
    MQZB = 32w1813085394;
    MQZB = 119w1392003097[46:15];
}
action AzRjG(inout bit<16> KvGT, inout bit<64> oFXm, out bit<8> ZeWM) {
    KvGT = 16w2588;
    ZeWM = 8w170;
    KvGT = ((bit<57>)1177252152)[32:17];
    ZeWM = (56w891622956 % 56w1197577582)[39:32];
}
parser SwitchIngressParser(packet_in pkt, out Headers hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        pkt.extract(ig_intr_md);
        pkt.advance(PORT_METADATA_SIZE);
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.IPIG);
        pkt.extract(hdr.GCXt);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    bool OrxVpK = !!true;
    action KsIzV(out bit<8> sOZO, out bit<128> NtnG, in bit<16> ELcu) {
        h.GCXt.BrQd = ELcu;
        bit<32> xkhZhU = (bit<32>)h.IPIG.KmYB;
        return;
        NtnG = 128w643424539;
    }
    action YoeGP() {
        if (!(OrxVpK && OrxVpK) && !!(67w699414965 != 67w1018304846)) {
            h.IPIG.vNOp = 8w204 << 8w7 * (8w201 |-| (8w183 | 8w233));
        } else {
            h.eth_hdr.eth_type = (71w978856051 |+| 71w545131237)[35:20];
        }
        h.IPIG.KmYB = h.IPIG.EXyN;
        {
            {
                bit<128> aiEhxR = 128w439411355 & (bit<128>)h.IPIG.vNOp;
                KsIzV(h.IPIG.vNOp, aiEhxR, 16w7231);
            }
            h.eth_hdr.dst_addr = (bit<48>)(!false ? 48w34818144 : 48w157399121 | h.eth_hdr.src_addr);
            h.IPIG.vNOp = 8w108;
            h.GCXt.BrQd = 34069 + h.GCXt.BrQd;
            h.IPIG.KmYB = h.IPIG.KmYB;
            h.eth_hdr.src_addr = 48w327307143;
            return;
            h.IPIG.vNOp = 74;
            h.IPIG.vNOp = 8w246;
            h.GCXt.BrQd = 32267;
        }
        bit<8> SuQgwe = h.IPIG.vNOp;
        h.GCXt.BrQd = h.eth_hdr.eth_type;
        return;
        h.eth_hdr.dst_addr = h.eth_hdr.src_addr |+| (bit<48>)(375439924 | (48w88617900 | h.eth_hdr.dst_addr)) >> (bit<8>)h.eth_hdr.dst_addr;
        h.eth_hdr.src_addr = 48w1175489741 - h.eth_hdr.dst_addr |-| h.eth_hdr.dst_addr;
        bool PWrdcb = OrxVpK;
        {
            bit<128> atGryA = -((bit<128>)SuQgwe |-| (128w460749163 >> (bit<8>)(bit<128>)h.eth_hdr.src_addr) |-| (bit<128>)h.eth_hdr.src_addr);
            KsIzV(SuQgwe, atGryA, h.GCXt.BrQd);
        }
    }
    table JImafd {
        key = {
            (true ? h.eth_hdr.eth_type : h.eth_hdr.eth_type - h.GCXt.BrQd): exact @name("lzWval") ;
        }
        actions = {
            YoeGP();
            AzRjG(h.eth_hdr.eth_type, h.IPIG.EXyN, h.IPIG.vNOp);
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        h.eth_hdr.setInvalid();
        h.IPIG.KmYB = (bit<47>)1791550628 ++ (bit<17>)h.eth_hdr.dst_addr;
        {
            h.GCXt.BrQd = 16w2864;
            h.eth_hdr.src_addr = h.eth_hdr.src_addr;
            h.IPIG.vNOp = 8w151 % 8w188;
            return;
            return;
            {
                bit<32> JabviN = 32w265215701 |+| (!((bit<126>)h.eth_hdr.src_addr - 126w465273443 == 126w327504574) ? 32w602219505 : 32w727780656);
                ygcMV(64w425908433, JabviN, h.eth_hdr.eth_type);
            }
            h.eth_hdr.src_addr = h.eth_hdr.dst_addr ^ 48w805077703;
        }
        h.eth_hdr.eth_type = 16w5016 - -(16w43160 + (16w17850 | 16w22245));
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

