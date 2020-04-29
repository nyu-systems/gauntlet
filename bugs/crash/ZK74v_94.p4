#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct yZAwcc {
    ethernet_t mhCj;
}

header UULema {
    bit<16> fldT;
    bit<16> mvPs;
    bit<64> nTlL;
    bit<64> SdIl;
}

struct yzhpIC {
    UULema WShw;
}

header hhaIGq {
    bit<16> eFgG;
    bit<32> Iqgf;
    bit<8>  VLJn;
    bit<32> vQYJ;
}

struct wkamyQ {
    hhaIGq MNGy;
}

header QkoXjl {
    bit<64> aKzF;
    bit<16> EtJy;
}

struct Headers {
    ethernet_t eth_hdr;
    UULema     fEoo;
    QkoXjl     WMJn;
}

struct Meta {
}

bit<16> IMsLfuF(in bit<128> jnKT, in int FuKt, in bit<32> hSkM) {
    bool YtOPhX = !false;
    ethernet_t krcsox = { FuKt, (bit<1>)1w1 |-| 1w1 ++ 47w1387374295, 16w64690 };
    if (YtOPhX) {
        if (YtOPhX) {
            krcsox.eth_type = 16w62544;
        } else {
            krcsox.dst_addr = 48w2063270338;
        }
    } else {
        krcsox.src_addr = krcsox.src_addr;
    }
    krcsox.dst_addr = krcsox.dst_addr;
    {
        krcsox.eth_type = ((!!!(YtOPhX || YtOPhX) ? 16w61008 |+| 16w53894 : krcsox.eth_type) | 16w30333) - 16w26098;
        krcsox.src_addr = (!YtOPhX ? 48w1760609350 |+| 48w1198769270 : (88w1296613624 != 88w291655328 ? 48w317804446 : 48w545203452));
        bit<128> msFkQe = jnKT;
        const int XlXKmJ = 712963600;
        krcsox.src_addr = ((bit<152>)477599192)[123:76];
        bool ixpuwo = !!!(!YtOPhX || true);
        krcsox.src_addr = 48w1355007716;
        krcsox.src_addr = krcsox.src_addr;
        return (true ? (53w2062380134 == 53w243221073 ? 98w1418186234 : (bit<98>)krcsox.eth_type)[47:32] : 16w32637) + 16w53319;
    }
    return krcsox.eth_type;
}
bit<4> CsOKcUm() {
    bool XCRhbc = !!false;
    const bit<32> WdoBlO = 32w123551205;
    bit<8> dqwnGB = (bit<8>)WdoBlO;
    {
        bit<128> oMSvbP = 128w2051693808;
        int qmHxrf = 1336299001;
        IMsLfuF(128w483017927, 1259217876, 32w1224627639);
    }
    dqwnGB = 45w60898730[17:10];
    dqwnGB = 8w196;
    dqwnGB = 8w183;
    dqwnGB = 47w2058530776[41:34];
    dqwnGB = 8w12;
    dqwnGB = 182;
    dqwnGB = dqwnGB;
    return 4w13;
}
bit<8> TVVaeIb(inout bool nDLn, inout bool Ocpe, out bool XTep) {
    if (!false) {
        ;
    } else {
        ;
    }
    CsOKcUm();
    bool VtiQbD = Ocpe;
    Meta wrHzoI = {  };
    bool JgXPiR = true;
    bit<16> rXZorh = 16w36194;
    rXZorh = 16w11382;
    rXZorh = rXZorh;
    rXZorh = 16w18915 |-| 16w60649;
    return ~(bit<8>)(bit<8>)153;
}
parser p(packet_in pkt, out Headers hdr, inout Meta m, inout standard_metadata_t sm) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.fEoo);
        pkt.extract(hdr.WMJn);
        transition accept;
    }
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    Meta vNsfxe = m;
    bool HZOPiB = !false;
    bit<32> UfuSog = (((true ? 32w294646891 : 32w911309702) | 32w449201009) >> (bit<8>)32w1397281962) |-| 32w1058114556;
    action HgPIw(inout ethernet_t plSM) {
        UfuSog = (bit<32>)CsOKcUm() - UfuSog;
        h.fEoo.SdIl = 64w1245874900;
        plSM.eth_type = (bit<16>)TVVaeIb(HZOPiB, HZOPiB, HZOPiB) - h.WMJn.EtJy |-| 16w49530;
        if (!true) {
            h.fEoo.mvPs = ((44w1219062627 | 44w2040384771) ^ 44w577440179)[18:3] + 16w49518;
        } else {
            plSM.src_addr = 48w1584829976;
        }
        {
            bit<128> DmGWAY = ~(128w399380790 * (false ? 128w1490808733 : 128w887125319));
            int ADWFsC = 1103808141;
            IMsLfuF(DmGWAY >> (bit<8>)1743603530, 1525183859, UfuSog);
        }
        {
            plSM.eth_type = 16w26422;
            const bit<16> gPMShc = 36458;
            if (!!true) {
                UfuSog = 32w1403583644 << (bit<8>)(-(bit<77>)UfuSog + (bit<77>)h.fEoo.nTlL)[65:34];
            } else {
                UfuSog = 32w348121724;
                const bit<128> kVUitN = 128w1235247043;
                UfuSog = UfuSog + 32w1182461874;
                return;
                const bit<128> EUndIc = 128w1725847111;
                h.eth_hdr.dst_addr = (bit<48>)(h.eth_hdr.src_addr - 48w1135229179);
                h.eth_hdr.eth_type = h.fEoo.fldT;
            }
            const bit<8> wsDpBw = 8w106 & 8w237;
            h.fEoo.nTlL = 108w393204382[74:11];
            UfuSog = ~(HZOPiB && true ? 32w1022078750 & 32w2088290065 : 32w2129107489);
            UfuSog = UfuSog;
            plSM.dst_addr = 48w742449178 / 48w900875376;
            plSM.src_addr = 48w2036104555;
        }
        bit<16> gqJIXc = 16w17616;
        h.WMJn.EtJy = 76w604559858[58:43] |-| h.eth_hdr.eth_type;
        const int aIJrjP = 1229858077;
        {
            UfuSog = 32w586218893;
            {
                UfuSog = UfuSog;
                plSM.eth_type = h.eth_hdr.eth_type + (16w39830 |-| 16w65216 | 16w64020);
                UfuSog = UfuSog;
                gqJIXc = (81w2067667176 == 81w1212223415 ? 16w46731 : (bit<16>)aIJrjP >> (bit<8>)(122w1754601464[75:60] >> (bit<8>)16w12126));
                plSM.src_addr = 48w327465235;
                h.eth_hdr.eth_type = (bit<16>)(16w46020 + aIJrjP) |-| gqJIXc;
                bit<128> RrHsrN = (bit<128>)h.fEoo.mvPs;
                return;
            }
            return;
            bool HbagNm = true;
            CsOKcUm();
            const bool SwzxPC = true;
            UfuSog = UfuSog;
            UfuSog = 967389737;
        }
    }
    action TEGFG(out bool vsiB, in bool TuSg, inout bool rBeN) {
        {
            h.fEoo.SdIl = 64w122186415;
            h.eth_hdr.dst_addr = 48w981797801;
            h.eth_hdr.dst_addr = 292164160;
            const bit<32> XjXBgF = 667920018;
        }
        h.eth_hdr.dst_addr = 48w1578208194;
        {
            bit<128> SxjCXF = 128w1852963017;
            int DYriFB = 2073866856;
            IMsLfuF(SxjCXF * SxjCXF, 460915776, ((bit<147>)IMsLfuF(128w1428305513 / 128w766693629, 733301330, (bit<32>)32w1148528232 |-| UfuSog - 32w1006249900))[143:112]);
        }
        UfuSog = 32w1972551591;
        h.fEoo.SdIl = 64w806865744 |+| 64w1434991317;
        UfuSog = 10w547 ++ 22w2548582;
    }
    table BjQdMe {
        key = {
            32w1757226356                  : exact @name("PDMPgY") ;
            (16w25719 & 16w7742) + 16w34779: exact @name("XiKkqB") ;
        }
        actions = {
            HgPIw(h.eth_hdr);
        }
    }
    apply {
        h.fEoo.fldT = 16w49797 | 107w42377192[52:37] | 16w7628;
        {
            bit<32> QJEcVj = UfuSog;
            h.WMJn.EtJy = 16w39646;
            TEGFG(HZOPiB, HZOPiB, HZOPiB);
            h.eth_hdr.dst_addr = h.eth_hdr.dst_addr;
            h.eth_hdr.eth_type = ((bit<16>)30105 >> (bit<8>)h.eth_hdr.eth_type) * (16w32987 % 16w37847);
            UfuSog = (bit<32>)CsOKcUm();
            TVVaeIb(HZOPiB, HZOPiB, HZOPiB);
            h.eth_hdr.src_addr = h.eth_hdr.dst_addr;
        }
        h.fEoo.mvPs = h.eth_hdr.eth_type |-| h.eth_hdr.eth_type;
        const bool pleZLE = 63w1230428578 != 63w1917762708;
        h.fEoo.mvPs = 16w57765;
        h.fEoo.SdIl = 64w2075743180;
        h.eth_hdr.dst_addr = 48w342592645 ^ 48w1782044729;
        bit<64> odDicp = ~64w926308628;
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

