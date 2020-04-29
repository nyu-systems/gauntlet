#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct QhbbJs {
    ethernet_t eOXB;
    ethernet_t wQlN;
}

struct NcoTFs {
    ethernet_t YKZk;
    ethernet_t xxQW;
    ethernet_t Gjgq;
    ethernet_t oYpp;
    ethernet_t fDBJ;
}

header NVsklI {
    bit<32>  BNBU;
    bit<128> asth;
    bit<16>  eNmO;
}

header WZaiDL {
    bit<16> GhOk;
}

struct Headers {
    ethernet_t eth_hdr;
    ethernet_t dctK;
    NVsklI     XvvO;
    WZaiDL     raim;
    WZaiDL     NEAq;
}

struct Meta {
}

bit<4> txDcCCH() {
    bool ZIJsjH = 6w13 | (bit<6>)57 >> 6w18 == 104w715218846[7:2] && true;
    bit<16> SfjYmI = 16w16467;
    SfjYmI = SfjYmI + SfjYmI;
    SfjYmI = SfjYmI;
    SfjYmI = SfjYmI;
    SfjYmI = (SfjYmI ^ (ZIJsjH ? 16w29367 << (bit<8>)16w37116 : 16w20482)) >> (bit<8>)16w55907;
    SfjYmI = 16w56432;
    bool iTvCXe = !!!ZIJsjH;
    return 4w3;
}
action oaByB(inout bit<16> YMXy) {
    YMXy = 16w32531;
    YMXy = (bit<16>)txDcCCH();
    YMXy = YMXy;
    YMXy = YMXy;
}
bit<16> NqvrnIL(in bool uMMg, out bit<16> NIRs) {
    NIRs = 16w7701;
    NIRs = NIRs * ((bit<16>)txDcCCH() - 16w33067) << (bit<8>)16w37256;
    NIRs = 16w3384;
    const int AnasPB = 2003096726;
    const bool ZSUbLI = 94w655905705 ^ 94w1502712743 == 94w58564821;
    if (!false) {
        NIRs = 16w45788 % 16w12532 & 16w55429 & 16w27873;
    } else {
        NIRs = AnasPB;
    }
    return NIRs;
}
action GErKF(in bool NJou, in bit<8> XHPq) {
    if (!!true) {
        ;
    } else {
        {
            bit<16> EUcbYo = 16w1335 - (bit<16>)XHPq;
            oaByB(EUcbYo);
        }
        bool MyJqnP = true;
        bool MVrSUV = (!!(43w262531143 != 128266065) || ((bit<29>)XHPq == 29w252087610 || MyJqnP)) && NJou;
        bool QFSzLY = !(96w1966945305 & (bit<96>)txDcCCH() == 96w567098939);
    }
    bool AihNCx = NJou;
    {
        bool ReUPdY = !NJou;
        txDcCCH();
        {
            bool KlOzdD = false;
            bool bTYAMk = (!ReUPdY ? 72w1653351749 >> (bit<8>)(bit<72>)XHPq : (bit<72>)XHPq) != (-88w2099660406)[78:7];
            if (!(AihNCx || false) || !!!!(104w476709263 == 104w525360333)) {
                ;
            } else {
                bool eJWOBA = 14w13380 == 14w11211;
                bit<64> OtPFCA = (bit<64>)txDcCCH();
                return;
                {
                    bit<16> uOPQnJ = (bit<16>)XHPq;
                    NqvrnIL(false, uOPQnJ);
                }
                {
                    bit<16> hsTXip = 16w4532 / 16w23800;
                    oaByB(hsTXip);
                }
                OtPFCA = OtPFCA;
                OtPFCA = ((bit<116>)OtPFCA)[106:43];
                {
                    const bool Scdxnq = !true || !!(!false && !!!false);
                    if (false && Scdxnq) {
                        bit<16> APNZoY = 16w27679 % 16w46820;
                        oaByB(APNZoY);
                    } else {
                        OtPFCA = 258w1105904877[243:86][70:7];
                    }
                    OtPFCA = (97w1650594382 != 97w1120970561 ? 64w1763041833 : (KlOzdD ? OtPFCA : OtPFCA));
                    OtPFCA = OtPFCA;
                    OtPFCA = 64w662533801;
                    OtPFCA = 64w1865292655 |-| OtPFCA;
                    const bit<128> OtOLGA = 128w754634970;
                }
                OtPFCA = 64w797045054;
            }
            {
                if ((!!false ? (219w1920303512 |+| (bit<219>)1386033200 |-| 219w1977293471)[190:63] : 128w889143934) != 128w950780384) {
                    ;
                } else {
                    bit<16> BSXTjG = 16w9100;
                    NqvrnIL(false, BSXTjG);
                }
                bool nHnIaP = !!!(false && !(false || !true) || true);
                return;
                bool OtgRwU = !!!!AihNCx;
                Meta fXhKpX = {  };
                bit<64> Gzmlbq = ~(bit<64>)XHPq;
                bit<8> qsdrFm = 8w193;
                qsdrFm = 8w64 << XHPq;
            }
            bool vWlpdA = true;
            const bool TCwfze = false;
            bool miUgqo = AihNCx;
            bool ugkdGn = !true;
        }
        {
            bit<16> WjUkeh = 16w47144;
            oaByB(WjUkeh);
        }
        bool AMlHOA = false;
    }
    bit<8> UeXvXg = 8w190;
    UeXvXg = 8w236 * ((bit<110>)187808245)[107:7][69:62];
    UeXvXg = 8w235;
    return;
    UeXvXg = ~(!true ? XHPq : (bit<8>)txDcCCH());
    if (false) {
        UeXvXg = XHPq;
    } else if (true) {
        UeXvXg = (bit<8>)txDcCCH();
    } else {
        UeXvXg = 8w66;
    }
}
parser p(packet_in pkt, out Headers hdr, inout Meta m, inout standard_metadata_t sm) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.dctK);
        pkt.extract(hdr.XvvO);
        pkt.extract(hdr.raim);
        pkt.extract(hdr.NEAq);
        transition accept;
    }
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    bit<16> SCDNiY = 16w62210;
    bool IAyMyh = true;
    bool mUwWEq = true;
    bool NjlNoh = true;
    bit<8> DLsGuQ = 183;
    action usGPB(inout bool syWd, in bit<128> eSCj, in bit<128> DjwN) {
        h.XvvO.BNBU = 32w1608192359;
        NqvrnIL(false, h.eth_hdr.eth_type);
        DLsGuQ = (false ? 76w794227995 : (bit<76>)txDcCCH() << (bit<8>)76w2143366295)[10:3];
        h.XvvO.BNBU = h.XvvO.BNBU;
        h.NEAq.GhOk = 16w54007;
        h.XvvO.asth = (((bit<244>)1560951793)[242:115] >> (bit<8>)128w919580383) |+| 174w379952602[144:17];
        h.eth_hdr.src_addr = (bit<48>)txDcCCH();
        bool duXFwI = !!syWd;
        bool xAZgKc = false;
    }
    table OluTJj {
        key = {
            16w51939: exact @name("CLtlUx") ;
        }
        actions = {
            oaByB(h.dctK.eth_type);
            usGPB(NjlNoh, 128w1603325323, 128w436858457);
            GErKF(false, 34w1194099567[12:5]);
        }
    }
    apply {
        h.XvvO.BNBU = h.XvvO.BNBU;
        h.XvvO.BNBU = (bit<32>)txDcCCH() | h.XvvO.BNBU;
        bit<16> iGrCOk = (bit<16>)NqvrnIL(IAyMyh, h.dctK.eth_type);
        h.XvvO.BNBU = 32w916681211;
    }
}

control vrfy(inout Headers h, inout Meta m) {
    apply {
    }
}

control update(inout Headers h, inout Meta m) {
    apply {
    }
}

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    apply {
    }
}

control deparser(packet_out pkt, in Headers h) {
    apply {
        pkt.emit(h);
    }
}

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

