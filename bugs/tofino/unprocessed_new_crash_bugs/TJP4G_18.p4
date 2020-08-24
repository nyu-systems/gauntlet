#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header NXoJKm {
    bit<128> rYug;
}

header AqngBl {
    bit<8>  JbVA;
    bit<64> OAnw;
    bit<64> XjLH;
    bit<16> uaRc;
    bit<64> Twmq;
}

header PkVRIh {
    bit<128> stVG;
}

header Onywmq {
    bit<32> vDRK;
    bit<64> aJKt;
    bit<32> rFpl;
}

struct IslGjx {
    PkVRIh  kkAw;
    bit<8>  fYGi;
    bit<32> nFjt;
    bit<64> fVAg;
}

struct Headers {
    ethernet_t eth_hdr;
    AqngBl     MmZS;
    PkVRIh     xSNy;
}

struct ingress_metadata_t {
}

struct egress_metadata_t {
}

bit<16> jQdviYo(bit<64> nJUx, bit<32> Oexh, bit<8> Mrbe) {
    bit<4> SzPOwB = ~4w11;
    const bool mLMXTS = true;
    bit<4> cdfqUT = 4w6 + SzPOwB |-| 4w12;
    SzPOwB = 4w1;
    cdfqUT = (mLMXTS ? 4w7 : cdfqUT + 4w10);
    cdfqUT = 4w3;
    return 16w54434 & (16w16591 & (bit<16>)Mrbe) + 16w22487;
}
bit<64> aTIVQBY(in bit<128> sWpZ, bit<16> QHJj, bit<8> FEqv) {
    jQdviYo(((-2099513444 ^ -1001714294) & 1242841011) + -1954826047, (!(83w5758669699133463595681975 != ((bit<215>)215w16869196942673068046130218084920920502473325526808784641045318654)[153:2][135:53]) ? 32w3774895795 : 32w2296885211 |-| 32w3114526473), 8w133 - 8w172);
    bool qOkPlH = false;
    jQdviYo(64w2842906577595123510 << (bit<8>)64w15522679948314190911, 32w2751909391, (bit<8>)8w91);
    jQdviYo(68w151502224009371912426[66:3], 32w149214355, 8w42);
    bit<32> kngLGb = 1465150560 + (1552892861 + 655964372 - -1421128495);
    return 64w13533542453804760779 % 64w11818035218101872605;
}
parser SwitchIngressParser(packet_in pkt, out Headers hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        pkt.extract(ig_intr_md);
        pkt.advance(PORT_METADATA_SIZE);
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.MmZS);
        pkt.extract(hdr.xSNy);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    bit<64> iYIvUI = h.MmZS.Twmq;
    bit<16> ZBUFHz = h.eth_hdr.eth_type;
    bit<64> bQvUPd = 64w4589140510995954210;
    bit<32> eCrjVB = 32w1691806147;
    bit<4> jkumUo = 4w6;
    bit<16> ZKgTVJ = 16w12149;
    action lYmYD(inout bit<128> MPlU, inout bit<16> kESx, bit<16> FKTH) {
        {
            eCrjVB = 32w3550379347;
            eCrjVB = eCrjVB;
            ZKgTVJ = 16w11993;
            bit<4> NTjmGy = 4w10 ^ 4w5;
            if (false) {
                aTIVQBY(MPlU, 16w46886, ((bit<99>)(99w296574711549226436953725563424 ^ 99w132313958723630966645305501341 + 99w548896733047038889785661574140 ^ 99w115205398856683564941325503338))[22:15]);
            } else {
                aTIVQBY((((bit<105>)eCrjVB & (105w26364194891463323857890290516094 | 105w23548613584775348542817897495360)) >> (bit<8>)105w39155810786785756969028705324411 != (bit<105>)h.MmZS.OAnw || false ? 128w297962901623195652081311825922518537640 : 128w125613268830973393377867941474721916791), 16w27049, 8w233);
            }
            return;
            jQdviYo(-64w4792144054995149413, 343869103 / 1158437799, 8w191);
            jQdviYo(64w11422250052774762173, (1243687767 | 1386049525) + -1792095125, 8w135);
        }
        const int nncmZU = -1841090335;
        bit<32> XfxgGj = 32w3685960312;
        eCrjVB[25:22] = (bit<4>)jQdviYo(64w1773005019208123347, 32w2078819694, (!false ? (bit<8>)8w106 : ((8w132 | 8w209) ^ 8w88) |-| 8w98));
        aTIVQBY((!!!!true ? 128w109099936585276569665550132237564809541 : 128w110423940932995271019515813598125386352), 16w45377 >> (bit<8>)((!true ? 16w38138 : 38w255672522477[28:13]) |+| 16w38400), 116w63698238824921294480743149664264599[22:15]);
        h.xSNy.stVG = MPlU |+| 128w138011434638292795150278829747884125103;
        jQdviYo(64w13031736331617968868 |+| -64w6789370141796556514, 32w1724836570, 8w222);
        jQdviYo(-((99w249784293135385286574110058830 != 99w413991827197390322728384950662 / 99w129165220707814688063991572265 ? 64w2150545327903951753 : 64w4872743662170142437) |+| 64w8623103643375756811), (~81w1825718083050514058218728)[68:37], 8w103);
    }
    action feZZR(out bit<64> nSRC, bit<16> GXqB) {
        const bit<4> JENnUa = (4w5 ^ 4w11 & 4w15) >> 4w3;
        h.xSNy.stVG = 380226191 + 724161061 + 128w134193590209329762470251096181604465711 ^ h.xSNy.stVG;
        jQdviYo(64w2518837882718195025, (!true ? (bit<86>)86w59916827254083376074913527 : 86w56877198423908810673092230)[33:2] & 32w3934652671, (false ? (bit<8>)(987753566 / 1031210094 - (-1687309356 ^ -1908834777)) : 8w62));
        jQdviYo(64w4079536436802813899, 32w1901991825 - 32w655475731, 8w27);
        jkumUo = (bit<4>)aTIVQBY((bit<114>)(-1036401041 & --1640905144 * 1221089554) ++ 14w2179, 16w41899 % 16w28544, ~8w114 & ((bit<8>)-713419051 |+| 8w61 | 8w60)) << 4w0;
    }
    action LSUtR() {
        ZKgTVJ = ZBUFHz;
        h.MmZS.JbVA = 8w224;
        h.eth_hdr.setInvalid();
        jkumUo = jkumUo |-| (bit<4>)(2001315856 % 1083539998);
        const AqngBl adaPnv = { 8w8, 64w11571154166578849800, 64w1030022978638247817, 16w924, 64w17127131352944196868 };
    }
    table aBvRuR {
        key = {
        }
        actions = {
            lYmYD(h.xSNy.stVG, h.eth_hdr.eth_type);
            LSUtR();
            feZZR(h.MmZS.XjLH);
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        iYIvUI = 64w772296196424085863;
        h.eth_hdr.dst_addr[37:30] = 8w21;
        h.MmZS.JbVA = h.MmZS.JbVA;
        h.MmZS.Twmq[61:46] = 16w19194;
        return;
        eCrjVB = eCrjVB;
        bit<8> KCeuxJ = 8w173;
        bQvUPd[42:27] = 16w40958 & ((bit<138>)jQdviYo(127w81874922801253853840497706834946630723[98:35], 32w807402074, ~8w253))[96:81];
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

