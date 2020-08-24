#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct fhzrDl {
    bit<32>    VWbi;
    bit<4>     OkJD;
    ethernet_t DwSr;
    bit<4>     kdln;
    bit<128>   uWri;
}

struct YOWdec {
    bit<128> Vbsr;
    bit<4>   KzLV;
    bit<32>  VebK;
    bit<32>  xiee;
}

header eTrPYQ {
    bit<32> gSDR;
    bit<32> GxrU;
    bit<64> CHfa;
    bit<4>  ciMi;
    bit<4>  padding;
}

header umOTlz {
    bit<32> wgzo;
    bit<64> lVwA;
    bit<32> BCEH;
}

header MZgQeK {
    bit<64> Jczb;
    bit<16> zzUr;
    bit<16> icvI;
    bit<4>  LpIx;
    bit<4>  padding;
}

header RMTUWx {
    bit<128> JPPt;
    bit<8>   JgtU;
    bit<32>  vOin;
    bit<16>  xujD;
}

struct Headers {
    ethernet_t eth_hdr;
    MZgQeK     Mmkr;
    eTrPYQ[2]  nwpG;
    umOTlz     wJvj;
    ethernet_t sWKI;
    ethernet_t QbrC;
}

struct ingress_metadata_t {
}

struct egress_metadata_t {
}

control oGgWzEf(inout bit<32> bXQY, bit<16> rhqw) {
    bit<64> KzAUFU = 64w6216160317638224889 |+| 64w15973673880984467875;
    bit<64> jKAJls = 64w9348431076250564129;
    bit<4> rIaxvS = 4w5;
    bit<8> mccEov = (bit<8>)jKAJls;
    bit<4> tCZXsR = 4w10;
    action rxsrv(bit<8> ENtH) {
        bXQY = 42w14986436020[35:4];
        umOTlz Rgkefw = { bXQY, 64w7070259479891362592 % 64w12272771321406769221, 32w472291271 };
        if (false || !true) {
            mccEov = mccEov;
        } else {
            tCZXsR = (!(61w75277547179094931 != ((bit<73>)(1815342577 / 856985544 & -1624022674))[63:3] || true) ? 4w10 : 4w1);
        }
        rIaxvS = ~4w8;
    }
    action bXEuE() {
        KzAUFU[23:16] = mccEov;
        mccEov = (false ? 8w158 : ((bit<52>)bXQY)[31:24]);
        jKAJls = KzAUFU;
        bit<32> RPnegC = 32w325946567;
        const bit<64> PbHtwS = ~(bit<64>)(64w15100139658132587589 % 64w8184087563217500565);
        rIaxvS = rIaxvS;
        mccEov = 8w162 * ((bit<39>)mccEov - 39w497574721290)[10:3] << 8w95;
    }
    action RFPti(bit<64> UBLZ, bit<16> VZvA) {
        mccEov = 479316176;
        KzAUFU = UBLZ;
        KzAUFU = 64w5292821131043249242;
        bXQY = 32w3161580183;
        return;
        mccEov = ~(bit<8>)8w19;
        jKAJls = 64w4760282591282365947;
    }
    table rKhieh {
        key = {
            64w2607332857865480773: exact @name("PVLvwo") ;
        }
        actions = {
            rxsrv();
        }
    }
    table uMwEbX {
        key = {
            8w127: exact @name("ODEAyO") ;
        }
        actions = {
            bXEuE();
            rxsrv();
        }
    }
    apply {
        egress_metadata_t Ctipti = {  };
        bit<16> zXOHiQ = rhqw |+| (16w4996 & 16w42602);
        zXOHiQ = (!!true ? 16w19385 : ~~16w15087) | 16w62646;
        mccEov = 8w152;
        jKAJls = 64w13215613627537248488;
        tCZXsR = tCZXsR;
        tCZXsR = rIaxvS;
        zXOHiQ = ((bit<65>)jKAJls |-| (bit<65>)65w33931967840166433849)[30:15];
        uMwEbX.apply();
        bXEuE();
    }
}

bit<32> CAuPsMc(bit<4> Nrlb) {
    bool lSnZct = !(33w2378581933 != 33w5088728853);
    const int PLUjwe = (110181457 | 155270381) + -1877123002 | -396407523;
    const bit<8> GSGMkh = (8w194 | 8w250) - 8w225;
    {
        bit<64> BdIUns = 64w16507779549445524352;
        const bit<32> QDGAhV = 32w1051667297 - 32w2639498807 & 32w1940994230;
        BdIUns = 64w11027040297094826840;
        BdIUns = PLUjwe;
        BdIUns = (bit<64>)(64w17514265110359780641 * 64w15272106531386175400) |+| 64w5120828294375424434;
        BdIUns = (lSnZct ? 64w12615585531354426102 : (bit<64>)(64w11006192200594219756 - -652450316 - 64w8277754363114307851));
        BdIUns = 64w16577097000726071455;
        BdIUns = BdIUns & 64w12752571153062277365;
        return QDGAhV;
    }
    bit<4> bIUGXa = ~Nrlb;
    bIUGXa = 4w8;
    bIUGXa = 4w4;
    bIUGXa = PLUjwe + -11639784;
    bIUGXa = (lSnZct && (lSnZct || !(49w153653860805306 != 49w110355667377122)) ? (bit<115>)(bit<115>)GSGMkh : 115w30125000689768735120325740568196646)[103:51][31:28] ^ 4w12;
    const bit<8> iGnRCL = 8w75;
    return 32w2402233829;
}
eTrPYQ jDNubiR() {
    bool JPVFxe = false;
    if (JPVFxe) {
        CAuPsMc(4w2);
    } else {
        ;
    }
    CAuPsMc(4w10);
    const bit<32> aqabBD = ~(32w2437590843 |+| 32w1355627608);
    return { aqabBD | aqabBD, aqabBD, 64w14826224129681153175 * ((false ? (bit<187>)aqabBD : 187w45594199422569687790034640932543710184014168164734702333)[98:35] & 64w16228258009357398699), (bit<4>)aqabBD, 4w1 };
}
parser SwitchIngressParser(packet_in pkt, out Headers hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        pkt.extract(ig_intr_md);
        pkt.advance(PORT_METADATA_SIZE);
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.Mmkr);
        pkt.extract(hdr.nwpG.next);
        pkt.extract(hdr.nwpG.next);
        pkt.extract(hdr.wJvj);
        pkt.extract(hdr.sWKI);
        pkt.extract(hdr.QbrC);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    bit<4> zTMsTA = h.Mmkr.LpIx;
    oGgWzEf() rCYEqP;
    action SYbTX(in ethernet_t BDgm, bit<32> yhgt, bit<4> Zzbn) {
        h.nwpG[1].padding = ((bit<60>)h.nwpG[1].ciMi)[43:40];
        h.sWKI.src_addr = BDgm.src_addr;
        bit<32> XWSwKK = (!!!!!!true ? 32w8996054 : 164w8227301762591926019243961327294002073189356102735[147:11][108:77] |+| 32w2446232631);
        h.sWKI.src_addr[32:1] = 32w4036020572 / 32w327682426;
        h.QbrC.dst_addr = ~h.sWKI.src_addr;
        h.nwpG[0].ciMi = h.Mmkr.LpIx;
    }
    action BwQaH(out bit<16> AGem, bit<16> gSsU, bit<4> MJvy) {
        h.nwpG[0].padding = (bit<4>)CAuPsMc((!(26w59490689 == 59w350524450943053111[51:26]) ? (bit<4>)-134622243 : 4w12 |+| (bit<4>)597937993 |+| 4w4));
        h.sWKI.eth_type = ~16w56185;
        h.wJvj.lVwA = 64w14290024296796134076;
        h.nwpG[0].GxrU = (!false ? -32w309133725 : h.nwpG[0].gSDR);
        h.nwpG[0].GxrU = h.nwpG[1].GxrU;
        h.sWKI.dst_addr = 48w16635428506842;
        bit<128> TAqVDR = (bit<128>)h.sWKI.src_addr;
        h.Mmkr.zzUr = 16w30736;
        return;
        h.nwpG[0].padding = h.nwpG[0].padding;
        h.nwpG[0].GxrU = -1666743942;
    }
    action MBvJq(bit<8> rgzH) {
        bit<32> FxbVkr = h.nwpG[1].gSDR;
        h.Mmkr.Jczb = 64w1574788051239013183;
        bool TAcJra = !!((bit<11>)h.eth_hdr.dst_addr == (bit<11>)h.Mmkr.zzUr);
        h.nwpG[1].padding = 4w0;
        h.Mmkr.padding = (bit<4>)zTMsTA |-| 108w324040283514856695181288516219572[104:3][79:76];
        const bit<64> loIxCS = 64w4140513374058933253;
        h.Mmkr.Jczb = 64w16132341713072522838;
        h.sWKI.dst_addr = 48w3360167316789;
        FxbVkr[26:23] = h.nwpG[1].padding;
        h.nwpG[1].ciMi = h.nwpG[0].padding |-| (4w9 ^ (bit<4>)CAuPsMc(4w1)) |-| 6w42[5:2];
        h.sWKI.eth_type = 16w52350;
    }
    table KVJJQo {
        key = {
        }
        actions = {
            BwQaH(h.Mmkr.zzUr);
            SYbTX({ 71w1221251288791957167948[62:15] | 48w275693234025051 >> (bit<8>)48w18950462334062 ^ 48w31149983842448, 48w11156366133688, -16w53155 * ((bit<5>)(5w15 + 2108763911) ++ 11w1153) });
        }
    }
    table OdQAfY {
        key = {
            64w5736891819795528986 % 64w6837917508102008482: exact @name("fzILDC") ;
        }
        actions = {
            BwQaH(h.QbrC.eth_type);
            SYbTX({ 48w69989186728746 >> (bit<8>)(false ? 48w121088790056047 : 48w208614980475297), 48w260762668353881, 16w6909 |-| (16w1643 |+| 16w17293) });
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        bool zKpKPm = !false;
        h.wJvj.BCEH = h.nwpG[1].gSDR & ((false ? 148w338672612532733291252948879133069180321853461 : 148w159013027496594519060316200621651785814820850) | (bit<148>)zTMsTA)[119:88];
        h.nwpG[1].padding = 4w10;
        h.wJvj.lVwA = 1907278879 - 2732539 / 721649270 & (1247881433 & -48657456);
        h.eth_hdr.eth_type = (-1394976442 + -209131332 + --1713754174) * 1217224247;
        jDNubiR();
        const bit<8> xxaYJp = (true ? (bit<8>)8w68 : 8w148);
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

