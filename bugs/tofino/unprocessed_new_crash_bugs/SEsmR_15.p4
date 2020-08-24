#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header GbtKhz {
    bit<4>  ciPx;
    bit<16> QxjZ;
    bit<4>  padding;
}

struct Slvvio {
    bit<8>  RTBT;
    bit<4>  LDPs;
    bit<32> tStK;
}

struct tIvIGA {
    bit<32> QIIv;
    bit<8>  szli;
    bit<64> craR;
}

header qYlXXA {
    bit<8>  BCru;
    bit<64> behs;
}

struct Headers {
    ethernet_t eth_hdr;
    ethernet_t tUpV;
    GbtKhz     VGnr;
    GbtKhz     ubUM;
}

struct ingress_metadata_t {
}

struct egress_metadata_t {
}

bool LzYeemz() {
    bool tBedJM = true;
    GbtKhz cDcxeA = { 4w10, 16w54982 |+| (16w19508 |+| (136w33063811149967579142076466822175608173919 * 136w68866714991971292620726248083806748533939)[34:19]), 4w15 | 4w11 + (4w5 + 4w8) };
    const bit<32> qmNTRV = (96w52974274789172700525181880213 == (1715447153 & -137672005) * 197560813 ? (bit<32>)32w677134622 : 32w119576119);
    cDcxeA.padding = 4w1;
    bit<4> KyIeJz = 4w11;
    cDcxeA.QxjZ = cDcxeA.QxjZ;
    return tBedJM;
}
bit<32> BqyKtGL(bit<32> XOVV, bit<8> aQlA, bit<16> YFbG) {
    bit<128> kPmXKc = (bit<128>)XOVV;
    if ((false || true) && true) {
        LzYeemz();
    } else {
        kPmXKc = kPmXKc;
    }
    return 32w3559759941;
    const bit<8> ckGXzq = 49w152448931318233[35:28] | 8w88;
    kPmXKc = 128w82665791298512191397073637736984153875;
    LzYeemz();
    LzYeemz();
    LzYeemz();
    kPmXKc = kPmXKc;
    kPmXKc = kPmXKc;
    kPmXKc = 128w150196192536636044637257324349614231426;
    return 32w2700274493;
}
control orOJYAC(bit<8> snMX) {
    bit<16> KGAAdS = 16w63885;
    bit<32> iuSdMG = ~32w1321933647;
    action umTZb(bit<64> EQmB) {
        iuSdMG = 32w1004886444 & (true ? ((bit<114>)iuSdMG)[57:26] : (bit<32>)(404262574 + iuSdMG));
        if (1014997848 != (bit<112>)KGAAdS) {
            KGAAdS = 1414288442 % 425924685;
        } else {
            KGAAdS = KGAAdS;
        }
        iuSdMG = (!!((true ? (bit<29>)29w230112248 >> (bit<8>)29w68255329 : 29w291387996) == 29w398981487) ? 32w1528900207 : iuSdMG) & 32w3055189476;
        KGAAdS = KGAAdS;
    }
    table FrwqrN {
        key = {
        }
        actions = {
        }
    }
    table uNGWMv {
        key = {
            16w39815                                                          : exact @name("asOFgU") ;
            ~8w10                                                             : exact @name("CPzYDQ") ;
            (!(true && LzYeemz()) ? 8w9 : snMX & 9w229[5:4] ++ (bit<6>)iuSdMG): exact @name("dZmklL") ;
        }
        actions = {
        }
    }
    apply {
        KGAAdS = 16w64253;
        BqyKtGL(~32w971141493, 8w223, (!false ? 16w44773 : 16w18773));
        KGAAdS = 16w32712;
        const bit<32> OLSvOT = 32w4204713227;
        const bit<8> ETVHdz = (!(10w497 == 10w571 | 56w30797697269875471[29:20] && !(!false && true)) ? 8w51 : 8w56);
        KGAAdS = (true || !!uNGWMv.apply().hit ? KGAAdS : 16w45302);
    }
}

bit<8> hmdPAKL(in bit<64> bRvt, inout bit<32> kCch, bit<8> FhPa) {
    bit<64> nJQYoS = 64w10521957523614114164 / 64w4929087637801047058;
    BqyKtGL((!false || !false ? 32w2650813340 : 32w3573661627 / 32w3326874162), 8w109, ~16w45295);
    kCch = ((bit<262>)FhPa ^ 262w695254916907758884099389247855172785332104910956831236565903989376807859556958)[256:104][130:99];
    nJQYoS = 64w1284148863431410869;
    kCch = kCch |-| 32w325870986 |+| (kCch ^ 32w297825435);
    kCch = 32w732719287;
    nJQYoS = 64w11050246917640717388;
    return (~(93w7245524095558352798235141898 != 93w9119688674405927185212594148 ? 81w1180841297152912527942818 : 81w1922158656899027730002790) & (bit<81>)FhPa)[76:69];
}
parser SwitchIngressParser(packet_in pkt, out Headers hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        pkt.extract(ig_intr_md);
        pkt.advance(PORT_METADATA_SIZE);
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.tUpV);
        pkt.extract(hdr.VGnr);
        pkt.extract(hdr.ubUM);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    bit<16> kMmnyo = 16w6433;
    bit<128> mgjQpw = (bit<128>)h.ubUM.padding;
    qYlXXA[6] zoAwwh;
    bit<32> APOCkm = 32w2743888939;
    bit<4> jXFyNu = 4w15;
    bit<4> akOFYF = jXFyNu;
    orOJYAC() vtbouB;
    orOJYAC() FWfbtX;
    action qkoLC(bit<4> LARK, bit<16> XZms) {
        zoAwwh[5].behs = 64w6806229781455499537;
        h.ubUM.ciPx = 4w8;
        const bit<16> ivFaDM = 16w57950;
        bit<8> hSeCMv = (true ? (bit<8>)8w99 : 8w234);
        bit<8> aQTaXH = 8w199 & 8w5;
    }
    action XWKQD(inout bit<4> eEIR, bit<32> SFMc) {
        h.ubUM.padding = (!!((bit<81>)(-2109075732 & 730056374) |-| 81w2270658859804134429825294 ^ 81w1659169031081896924628714 == (bit<81>)mgjQpw) ? 4w4 : 4w13);
        bool pvrYps = !!false;
        BqyKtGL(32w1466215178, 8w212, 16w19229 |-| (bit<16>)160497730);
        hmdPAKL(64w186194980496478465, APOCkm, 1099762488);
    }
    table MDfvDR {
        key = {
            16w29991              : exact @name("vQGDWW") ;
            64w6509730919774624803: exact @name("IPIkqE") ;
        }
        actions = {
            XWKQD(zoAwwh[1].BCru[3:0]);
        }
    }
    table wONoYU {
        key = {
        }
        actions = {
            qkoLC();
        }
    }
    table uokqzI {
        key = {
            8w20: exact @name("zFlwbF") ;
        }
        actions = {
        }
    }
    table qJpDtJ {
        key = {
        }
        actions = {
            XWKQD(h.VGnr.ciPx);
            qkoLC();
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        FWfbtX.apply(8w147);
        h.tUpV.dst_addr = (bit<48>)h.eth_hdr.dst_addr |-| ((bit<48>)hmdPAKL(15w7131 ++ (LzYeemz() ? 54w15252835046181179[49:1] : 49w94454172229398 % 49w339370600610534), APOCkm, 8w218) - (48w258991247391467 | 48w277958847250483)) & (false ? (bit<48>)1220296327 : h.tUpV.dst_addr);
        h.tUpV.dst_addr = ((bit<73>)h.VGnr.ciPx)[64:17] |-| (!LzYeemz() || (true || !!!true && 12w1975 + 12w2590 != 12w951) ? 48w210426606603038 : 48w193735680098108);
        switch (wONoYU.apply().action_run) {
            qkoLC: {
                BqyKtGL(32w4070793410 / 32w1990613535, (bit<8>)(bit<8>)351638541 >> 8w82 |+| 8w204 + 8w178, 16w31304);
                bit<64> dEjhnq = zoAwwh[4].behs;
                APOCkm = 2031720505 / 561728243 - 263544686 - -459078821;
                const bit<16> jNJqLB = 16w9234 & 16w8198;
                h.tUpV.eth_type = -1025697934;
                switch (uokqzI.apply().action_run) {
                }

                LzYeemz();
                h.VGnr.QxjZ = 16w46330;
                h.VGnr.QxjZ = -1350662826 ^ ~(bit<16>)h.ubUM.QxjZ;
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

