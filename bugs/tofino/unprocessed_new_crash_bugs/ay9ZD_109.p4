#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>


header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct tybkNy {
    ethernet_t SHWL;
    ethernet_t MaFQ;
    ethernet_t bcdx;
    ethernet_t tSzC;
    ethernet_t jOxy;
}

header vZTIYI {
    bit<8>  HfpI;
    bit<16> pMEQ;
}

struct NoCHoE {
    ethernet_t XvAV;
    ethernet_t Yuyg;
    ethernet_t ijdp;
    vZTIYI     OJQD;
    vZTIYI     UUJd;
}

struct xIRNow {
    ethernet_t jYhO;
    ethernet_t Eoda;
    ethernet_t oEMo;
    vZTIYI     VFxS;
}

struct tbffAP {
    vZTIYI     qDUC;
    ethernet_t skdR;
    ethernet_t RWqn;
    ethernet_t uzao;
    vZTIYI     HOOJ;
}

struct RQOufm {
    vZTIYI     iGmx;
    vZTIYI     yasO;
    vZTIYI     qFjc;
    ethernet_t iCsH;
    vZTIYI     GxTp;
}

struct LglqSV {
    ethernet_t ZjaA;
    ethernet_t cUYw;
    vZTIYI     FfOh;
}

header QBYCjW {
    bit<64>  AlIg;
    bit<128> zTbY;
}

struct Headers {
    ethernet_t eth_hdr;
    vZTIYI     oFwN;
    QBYCjW     iSIw;
    ethernet_t yocW;
    QBYCjW     nsQo;
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
        pkt.extract(hdr.oFwN);
        pkt.extract(hdr.iSIw);
        pkt.extract(hdr.yocW);
        pkt.extract(hdr.nsQo);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    bit<128> yeTdfv = (491752982 ^ ((bit<231>)(77023701 + 231w199541681))[216:65])[133:6];
    bool cxmhTF = false;
    bool VIVWFB = !false || (cxmhTF ? -124w887654372 : ((bit<177>)h.yocW.eth_type)[137:14]) != 124w2082727345;
    bool jcnkdm = VIVWFB;
    LglqSV jwPfBL = { { h.yocW.dst_addr, (!cxmhTF ? h.eth_hdr.dst_addr : h.eth_hdr.src_addr), 16w24741 }, { h.eth_hdr.src_addr, 48w607422551, 16w30949 - -16w22013 }, { h.oFwN.HfpI, 16w201 } };
    action VLNrk() {
        bool YIZKSj = 91w362233430 == (bit<91>)jwPfBL.FfOh.HfpI;
        return;
        h.eth_hdr.dst_addr = 48w591189758;
        if (false) {
            jwPfBL.FfOh.pMEQ = 16w44791;
        } else {
            h.yocW.dst_addr = ((bit<141>)h.nsQo.AlIg)[92:45] & ~jwPfBL.ZjaA.dst_addr;
        }
        yeTdfv = 128w1525945500;
        h.oFwN.pMEQ = ~16w34288;
        jwPfBL.FfOh.pMEQ = ~jwPfBL.cUYw.eth_type;
        return;
    }
    action oCxmQ(inout bit<128> nklL, out bit<32> NGhv, in bit<16> hdVI) {
        return;
        h.iSIw.AlIg = ~-(127w535271328[85:22] |-| (bit<64>)1135126319);
        return;
        h.nsQo.AlIg = 64w1736024823;
        if (!true) {
            jwPfBL.ZjaA.dst_addr = 48w468952232;
        } else {
            jwPfBL.ZjaA.dst_addr = 48w98143484 & (48w1034891424 | (!!false ? 48w1092094917 : 48w1774863483)) ^ 48w1629828173;
        }
        jwPfBL.FfOh.HfpI = h.oFwN.HfpI;
        h.eth_hdr.src_addr = 48w1408874834;
        h.oFwN.HfpI = 8w209;
        h.iSIw.zTbY = h.iSIw.zTbY ^ 140w2111088621[128:1] |-| yeTdfv;
    }
    table xpOuND {
        key = {
            (29w180119261 ++ (bit<35>)jwPfBL.ZjaA.src_addr * (bit<35>)h.yocW.eth_type ^ 64w1121367602) & 64w523102629: exact @name("leleCt") ;
            (jcnkdm ? 128w1111751349 : 128w307708773)                                                                : exact @name("wpcBfc") ;
            48w1090091053                                                                                            : exact @name("RgCtvq") ;
        }
        actions = {
            VLNrk();
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        h.oFwN.HfpI = 8w114;
        h.nsQo.zTbY = (!((bit<53>)jwPfBL.cUYw.src_addr == (bit<53>)jwPfBL.ZjaA.eth_type) ? 88w732716515 + 88w1544195785 |-| 88w592219509 : 88w1822807568) ++ 40w968268228;
        VLNrk();
        VLNrk();
        jwPfBL.FfOh.HfpI = jwPfBL.FfOh.HfpI | (12w558 ++ 87w45123767 / 87w454448703)[41:34];
        {
            if ((bit<33>)h.yocW.src_addr != 33w2132221270) {
                jwPfBL.cUYw.eth_type = jwPfBL.cUYw.eth_type;
            } else {
                bit<32> hiEgMP = (bit<32>)h.nsQo.AlIg;
                oCxmQ(yeTdfv, hiEgMP, 16w22253 + jwPfBL.cUYw.eth_type);
            }
            h.oFwN.HfpI = 8w241 % 8w175;
            h.yocW.src_addr = jwPfBL.ZjaA.src_addr ^ (-48w546908320 | 48w518218882);
            h.nsQo.AlIg = h.iSIw.AlIg;
            {
                h.oFwN.HfpI = (bit<8>)jwPfBL.FfOh.HfpI ^ h.oFwN.HfpI;
                if (!(!true && !!!VIVWFB)) {
                    bit<32> HXXTOU = (!!cxmhTF ? -32w825180241 : 32w1146464110);
                    oCxmQ(yeTdfv, HXXTOU, 59925);
                } else {
                    yeTdfv = 128w1865107396;
                }
                h.nsQo.AlIg = 64w1047021474;
                h.nsQo.AlIg = h.iSIw.AlIg;
                h.oFwN.pMEQ = ~16w32817 - h.oFwN.pMEQ;
                h.iSIw.zTbY = 1760996429;
                h.eth_hdr.eth_type = 53244;
                bool rdrOwF = !!false;
                yeTdfv = 128w1669331795 % 128w1599613552;
            }
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

