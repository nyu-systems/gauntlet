#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>


header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct AvxiEy {
    ethernet_t yjyH;
    ethernet_t JAOB;
    ethernet_t mEVb;
    ethernet_t xMMj;
}

header YiYvKT {
    bit<32>  szTV;
    bit<128> TFVc;
}

struct eAyKVB {
    YiYvKT SNTd;
    YiYvKT TLvO;
    YiYvKT qiqS;
    YiYvKT LsHe;
}

struct EGHQMH {
    ethernet_t yErF;
}

struct Headers {
    ethernet_t eth_hdr;
    YiYvKT     AcfT;
    ethernet_t CJNU;
}

struct ingress_metadata_t {
}

struct egress_metadata_t {
}

action mVOeF() {
    ingress_intrinsic_metadata_for_deparser_t JanZPW;
    bit<32> paKvYq = 32w147394101;
    bool TQzEFU = !false;
    if (TQzEFU && !TQzEFU) {
        paKvYq = paKvYq;
    } else {
        paKvYq = 32w904450388;
    }
    paKvYq = 32w763754874;
    paKvYq = 32w1689926189;
    if (!!!true) {
        paKvYq = 32w1622810432 & ~paKvYq;
    } else {
        paKvYq = paKvYq;
    }
    bit<64> EOxfTC = (bit<41>)paKvYq ++ 23w6459488;
}
parser SwitchIngressParser(packet_in pkt, out Headers hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        pkt.extract(ig_intr_md);
        pkt.advance(PORT_METADATA_SIZE);
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.AcfT);
        pkt.extract(hdr.CJNU);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    bool BywniC = !!(36w1495022002 ^ (bit<15>)h.AcfT.TFVc ++ (bit<21>)h.AcfT.TFVc != 36w1565007823);
    bool XtoCoq = BywniC;
    egress_intrinsic_metadata_for_deparser_t ckxMHN;
    action XqpvF(inout bit<16> xyKf, inout bit<8> ZXhw, out bit<8> IMds) {
        h.AcfT.TFVc = 128w558533583;
        h.CJNU.src_addr = h.CJNU.dst_addr + ((bit<123>)h.AcfT.TFVc != (bit<123>)IMds ? (bit<48>)1807087853 : h.eth_hdr.dst_addr);
        h.AcfT.szTV = 32w61437983;
        h.AcfT.szTV = (false ? 32w1653489537 : h.AcfT.szTV) - 32w1085331922;
        h.AcfT.TFVc = (!BywniC ? 128w1759437021 : (bit<128>)695378307);
    }
    table qpYDbK {
        key = {
            h.AcfT.szTV: exact @name("iEXeKv") ;
            16w17640   : exact @name("jPmzeO") ;
        }
        actions = {
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        h.CJNU.dst_addr = (h.CJNU.dst_addr ^ 48w98400261) - 48w1596479250;
        h.CJNU.src_addr = h.eth_hdr.dst_addr;
        h.CJNU.eth_type = 98w1659271169[39:24] + h.CJNU.eth_type;
        if (BywniC) {
            h.AcfT.szTV = 32w1724138174;
        } else {
            h.CJNU.eth_type = 16w34726;
        }
        bool NHxDYV = true || !(true && XtoCoq);
        h.eth_hdr.src_addr = ((bit<94>)(945376571 | 94w1533103542 % 94w716554903))[87:40] |-| 48w1594100480;
        h.AcfT.TFVc = 210w283199224[200:73];
        bit<32> FkGpeq = (true ? h.AcfT.szTV ^ (!false ? 32w147932391 : 32w560575556) : h.AcfT.szTV);
        h.AcfT.szTV = h.AcfT.szTV;
        h.AcfT.TFVc = 128w113500262;
        h.eth_hdr.eth_type = 11804;
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

