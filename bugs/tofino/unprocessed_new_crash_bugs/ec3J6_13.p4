#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header zUBEAk {
    bit<64> okqC;
    bit<8>  jbKL;
    bit<16> xIjd;
}

struct kQxZRN {
    bit<4> kQMQ;
    bit<8> zxOA;
}

header oDNYGB {
    bit<4> bAiA;
    bit<4> padding;
}

header aVYgQt {
    bit<32> GwgS;
}

header wADMzl {
    bit<16> pKUb;
    bit<64> pMYL;
    bit<16> qyFh;
    bit<16> hGlM;
    bit<32> CCBy;
}

struct Headers {
    ethernet_t    eth_hdr;
    ethernet_t    VnoD;
    wADMzl        MaAJ;
    ethernet_t[9] jpWh;
    aVYgQt        YQIX;
}

struct ingress_metadata_t {
}

struct egress_metadata_t {
}

bit<128> InGWwLX() {
    bit<8> EoKLZl = 8w90 - (8w138 << 8w112);
    EoKLZl = 8w54;
    EoKLZl = 8w198;
    return 128w184017895070803005349058959146909746667;
    EoKLZl = EoKLZl << 124w1465458024213907090162685281942085054[18:11];
    bit<8> mHJCLf = EoKLZl & 8w192 ^ 8w240 - (8w192 ^ EoKLZl);
    EoKLZl = 8w15;
    bit<16> KboIvd = 16w19712;
    mHJCLf = (true ? EoKLZl : 1w1 ++ 7w94) |-| 30w979090035[8:1];
    return 128w211782673623067153299352561200637297638;
}
bit<16> dloNUyB() {
    bool MSCJdW = !true;
    ethernet_t[5] uHDTlq;
    uHDTlq[0].dst_addr = uHDTlq[3].src_addr - 48w143015035999276;
    uHDTlq[1].eth_type = 16w38058;
    uHDTlq[1].eth_type = 16w65129;
    const bit<8> tObEAY = ~(127w23949520606020744771176773945562195818 % 127w74059301495062001709391931590192542205)[45:38];
    bit<64> dxnpvW = 64w11140408940197325013;
    const bool yJBWLA = !!(!true || !false);
    InGWwLX();
    InGWwLX();
    return uHDTlq[3].eth_type;
}
bit<8> tQNOQXT() {
    bit<8> lsfdZA = 8w224;
    const ingress_metadata_t DbePkK = {  };
    lsfdZA = 8w111;
    lsfdZA = lsfdZA ^ lsfdZA;
    lsfdZA = (!!false && false ? lsfdZA : (bit<8>)-1651396738);
    lsfdZA = 8w33;
    lsfdZA = (bit<8>)((bit<35>)lsfdZA)[10:3] |+| lsfdZA;
    const bit<4> IshvDf = -1249663823;
    return lsfdZA;
    lsfdZA = lsfdZA;
    InGWwLX();
    return (bit<8>)InGWwLX();
}
parser SwitchIngressParser(packet_in pkt, out Headers hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        pkt.extract(ig_intr_md);
        pkt.advance(PORT_METADATA_SIZE);
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.VnoD);
        pkt.extract(hdr.MaAJ);
        pkt.extract(hdr.jpWh.next);
        pkt.extract(hdr.jpWh.next);
        pkt.extract(hdr.jpWh.next);
        pkt.extract(hdr.jpWh.next);
        pkt.extract(hdr.jpWh.next);
        pkt.extract(hdr.jpWh.next);
        pkt.extract(hdr.jpWh.next);
        pkt.extract(hdr.jpWh.next);
        pkt.extract(hdr.jpWh.next);
        pkt.extract(hdr.YQIX);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    aVYgQt[5] ERvFzt;
    bit<4> ApMmjN = 4w7;
    bit<128> deEOwP = 128w90855157942001768367818954565431586919;
    action XGnNr(in bit<8> qrol, bit<128> YbfM) {
        InGWwLX();
        return;
        const bit<64> IEiBpo = ((bit<146>)237844269)[82:19];
        const bit<16> UiddFb = 16w16419;
        h.MaAJ.pMYL = IEiBpo;
    }
    action ExbrK(bit<16> kvHK, bit<8> RUiP, bit<128> Irjz) {
        h.jpWh[0].dst_addr = 48w225283149674494;
        return;
        h.VnoD.eth_type = 16w30451;
        const bit<8> ldsgiV = 8w218;
        ApMmjN = -ApMmjN;
        ERvFzt[4].setInvalid();
        h.MaAJ.CCBy = 32w3558487002;
        h.jpWh[0].src_addr = 1473745062 / 2127847978 - 358218632 - -1950318977 + 48w109455690959719;
        ERvFzt[2].GwgS = 32w1811414369;
        ApMmjN = (bit<4>)InGWwLX();
    }
    action GPuki(bit<64> pbip) {
        const int TaNsSJ = 16350527 / 1348282918;
        h.jpWh[6].src_addr[30:15] = (bit<5>)5w29 ++ 11w1263 / 11w66 | ~16w8626;
        h.jpWh[3].eth_type = 16w52510;
        bit<64> KtEIMJ = h.MaAJ.pMYL;
        ERvFzt[0].GwgS = h.YQIX.GwgS;
        ERvFzt[2].GwgS = ERvFzt[4].GwgS;
        h.VnoD.dst_addr = h.jpWh[0].dst_addr | h.jpWh[7].src_addr;
        bool MsiPQt = true;
    }
    table KSTVJV {
        key = {
            128w306251629934827074512349941323396882702 % 128w323203221192664197397203010572335905009: exact @name("pvIplT") ;
        }
        actions = {
        }
    }
    table SFzmcH {
        key = {
        }
        actions = {
            GPuki();
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        const bool pONmjP = true;
        ApMmjN = (!KSTVJV.apply().hit ? ((bit<127>)ApMmjN)[110:107] : ApMmjN & ApMmjN);
        switch (SFzmcH.apply().action_run) {
            GPuki: {
                h.MaAJ.pMYL[60:13] = (false || true ? h.jpWh[4].src_addr : h.jpWh[6].dst_addr);
                bit<128> qKpGHD = deEOwP ^ deEOwP;
                qKpGHD = 128w325951403381932798439886476372977886014;
                bit<128> TLVoHg = deEOwP;
                ApMmjN = 4w2 % 4w9;
                InGWwLX();
                tQNOQXT();
                ApMmjN = ApMmjN;
                tQNOQXT();
                bit<128> fxqznh = deEOwP;
                h.MaAJ.CCBy = 55w16468854645031152[53:22] |-| (32w3772378960 << (bit<8>)32w4041010647) + 32w40346191;
            }
        }

        h.VnoD.eth_type = (bit<16>)InGWwLX();
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

