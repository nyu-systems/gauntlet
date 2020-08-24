#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header WrLjrv {
    bit<64> ZmTx;
}

header cAqKuF {
    bit<32> CcCo;
    bit<32> BExK;
    bit<16> AFcj;
    bit<32> iElF;
    bit<16> zmtO;
}

header ADhtVn {
    bit<32> Hbsv;
    bit<64> lTKO;
}

struct ESDmxz {
    bit<64>  uzKA;
    bit<8>   UlBc;
    bit<32>  HSNe;
    bit<128> Gquv;
    bit<128> Yttf;
}

header qfoajS {
    bit<16>  hqpM;
    bit<128> jbQd;
    bit<16>  Wikt;
    bit<128> dXLN;
}

header wTAbcY {
    bit<32>  mTtG;
    bit<128> gWPE;
}

struct Headers {
    ethernet_t eth_hdr;
    ADhtVn     wjEF;
    qfoajS     REKU;
    WrLjrv[8]  Myng;
    cAqKuF     DdBQ;
    wTAbcY     PSER;
}

struct ingress_metadata_t {
}

struct egress_metadata_t {
}

action qwqTo(bit<16> exAy, bit<4> Pohr) {
    ESDmxz KUnywC = { -(bit<64>)Pohr, (bit<8>)Pohr, 32w3139411965, (bit<128>)exAy, (-(bit<246>)exAy)[222:95] |+| 128w320880753887335659894481502132700588590 };
    KUnywC.HSNe = KUnywC.HSNe;
    KUnywC.UlBc = 8w178;
    {
        KUnywC.uzKA = 64w18201241340341809202 |-| KUnywC.uzKA;
        KUnywC.Yttf = KUnywC.Gquv;
        bit<128> yDbCbR = KUnywC.Gquv;
        KUnywC.HSNe = 32w3465213478;
        KUnywC.uzKA = KUnywC.uzKA >> (bit<8>)((bit<162>)KUnywC.uzKA)[74:11];
    }
}
bit<128> gmIGIlO(bit<4> ZXBA) {
    if (!(true || !(-(bit<24>)ZXBA != 24w6793587 / 24w15956838))) {
        ;
    } else if (false) {
        ;
    } else {
        ;
    }
    const WrLjrv hJosnG = { 64w2084063288183524674 };
    bit<16> kXefPI = ((bit<33>)hJosnG.ZmTx)[22:7];
    kXefPI = kXefPI;
    kXefPI = 16w45365;
    bit<4> PGMpjr = 4w13;
    bit<64> PsxuFu = hJosnG.ZmTx >> (bit<8>)64w7450888222341450283;
    kXefPI = ((bit<47>)ZXBA)[28:13];
    PsxuFu = 64w15788212964371350361;
    PsxuFu = 64w605495312702848003 + (7w126 % 7w113 ++ 57w103324231261264260);
    kXefPI = 16w47481;
    return (false ? (false ? 128w4426163720068725207833988225764651260 : (bit<128>)kXefPI) : 128w200993412404902965468342367363136537192);
}
ESDmxz ApKzqZK(inout bit<16> AWYX, inout bit<32> Usog, bit<4> jzVD) {
    AWYX = AWYX;
    AWYX = AWYX;
    gmIGIlO(4w1 << 4w14 ^ 4w12);
    Usog = 32w2492138095;
    return { (bit<64>)Usog, 8w168, (true ? 32w3180883818 : Usog), 128w261495711198132635229786657612518786722, (bit<77>)Usog ++ ((bit<51>)Usog << (bit<8>)51w1885481144654808) };
}
parser SwitchIngressParser(packet_in pkt, out Headers hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        pkt.extract(ig_intr_md);
        pkt.advance(PORT_METADATA_SIZE);
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.wjEF);
        pkt.extract(hdr.REKU);
        pkt.extract(hdr.Myng.next);
        pkt.extract(hdr.Myng.next);
        pkt.extract(hdr.Myng.next);
        pkt.extract(hdr.Myng.next);
        pkt.extract(hdr.Myng.next);
        pkt.extract(hdr.Myng.next);
        pkt.extract(hdr.Myng.next);
        pkt.extract(hdr.Myng.next);
        pkt.extract(hdr.DdBQ);
        pkt.extract(hdr.PSER);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    ethernet_t NQvQTw = { 48w81136818122821, 48w142837261108179, h.REKU.hqpM };
    bit<128> gnhqpo = h.PSER.gWPE;
    bit<32> hTTZdQ = (true ? 32w4023681762 : (bit<32>)805056899) & 32w572240721 >> (bit<8>)123w7354125315847276461452084402827267630[40:9];
    bit<128> WuyHJs = h.REKU.jbQd + ((bit<256>)-1693370622)[181:54];
    bit<128> kDufdh = 128w323464620099024241831636847664591592110;
    bit<128> MltzXj = -948151020;
    action udaOh(in wTAbcY PvoK, out bit<4> PlXE, bit<32> WaGI) {
        ADhtVn GEMIdf = { (bit<32>)32w3101177286, (true ? (bit<64>)(h.Myng[0].ZmTx | -951798826) : (true ? h.Myng[4].ZmTx : (bit<64>)(1305689224 - -810335836))) };
        ApKzqZK(h.eth_hdr.eth_type, h.DdBQ.iElF, 4w0 - 4w5);
        NQvQTw.eth_type = (false ? h.REKU.Wikt : (bit<16>)(1064617234 * 1410020190 | 16w14557));
        h.eth_hdr.dst_addr = 48w195718349932799;
        h.eth_hdr.dst_addr = 48w84608769740750;
        if ((bit<123>)h.REKU.Wikt != (!!(64w12730332317660023288 != 145w29996714368204400986226179056217015635261358[98:35]) ? 123w4448186574330016323699465843405028063 & 123w4688473084360260493113153147349203984 | 123w9656883157353392837882280837956132965 : (bit<123>)GEMIdf.Hbsv)) {
            h.DdBQ.AFcj = h.DdBQ.AFcj;
        } else {
            h.Myng[1].setValid();
        }
    }
    action NFyGP() {
        h.eth_hdr.dst_addr = h.eth_hdr.src_addr;
        gmIGIlO(4w9);
        bit<8> fuKwoR = (bit<8>)h.DdBQ.AFcj;
        fuKwoR = (false ? 8w31 : 8w244);
    }
    action YOeYX(bit<16> PvFm) {
        bit<4> QNjcOc = 4w12 & 4w1;
        const bit<4> jxKvnH = 4w4;
        bit<8> Uvlsqs = (95w12793194243516646941631556667 ++ ((35w15408032389 << (bit<8>)(bit<35>)QNjcOc) - (bit<35>)jxKvnH))[42:35];
        kDufdh[36:5] = h.DdBQ.BExK;
        h.REKU.Wikt = (16w10906 & PvFm) |-| (true ? 16w43751 : (bit<16>)-1353268374) ^ 16w32523;
        const bit<64> FCKidj = 64w5964775920314462291;
    }
    table DJhFgN {
        key = {
            16w46567 + NQvQTw.eth_type: exact @name("rlSsbt") ;
        }
        actions = {
            NFyGP();
        }
    }
    table aNlutI {
        key = {
            32w1320044912: exact @name("vUdAtm") ;
        }
        actions = {
            NFyGP();
        }
    }
    table nbMTHi {
        key = {
            128w14726960554159126996232947545646520040: exact @name("ZmABZM") ;
            32w2359334700 + 32w3761910850             : exact @name("hZGjZt") ;
        }
        actions = {
        }
    }
    table WlDAYK {
        key = {
            h.eth_hdr.dst_addr     : exact @name("BqyhTx") ;
            64w11073614974031672789: exact @name("QrjxaJ") ;
            h.Myng[5].ZmTx         : exact @name("GWJYwN") ;
        }
        actions = {
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        h.Myng[6].ZmTx = 64w3652276301479910032;
        {
            h.REKU.jbQd[72:9] = 137w13349321535452665456033265222331057185979[103:40];
            WuyHJs = 128w2949817851938230321320043361772758353;
            hTTZdQ = 32w2350504194;
            gnhqpo = 186w69840311456690978352147295137996262543764722079954441015[168:41];
            gmIGIlO(4w7);
            h.Myng[1].ZmTx = h.Myng[2].ZmTx |+| (64w15316467812201035566 - 64w7059040616572421158);
            h.REKU.hqpM = 16w36314;
            if (37w43051116417 == 37w110648904962 & -95813918) {
                h.REKU.Wikt = -1099651203 | -661000552;
            } else if (!true) {
                if (68w174702316607501635947 != -(-1993418176 * (bit<68>)h.eth_hdr.eth_type)) {
                    h.DdBQ.AFcj = (bit<16>)(16w6255 * 16w54690) |+| (bit<16>)(-1550612190 - -1661537201 | -35902770);
                } else {
                    MltzXj = 128w245944809957630027698675624082230712146;
                }
                bit<4> ABVpqp = 4w12;
                h.Myng[7].ZmTx = 64w12304958703260287392 + 135w25025192139378042980182649831134737028562[90:27];
                gmIGIlO(4w14);
                bit<8> xIHVMD = -8w172 - 8w110;
                ApKzqZK(NQvQTw.eth_type, hTTZdQ, -(bit<4>)(4w3 * (-716498627 ^ 1641557335)));
                h.Myng[5].ZmTx = 64w3403781028152825308;
                h.PSER.gWPE[96:33] = 64w11687134715554833237;
            } else {
                ApKzqZK(h.DdBQ.AFcj, h.DdBQ.iElF, 4w2 + 1295828152);
            }
            const bit<32> pUNJBz = 32w198005139;
            NQvQTw.dst_addr = h.eth_hdr.dst_addr;
            h.DdBQ.BExK = 32w446644097;
        }
        NQvQTw.src_addr = 48w81977037996790;
        gmIGIlO((bit<4>)4w8 >> 1961579618);
        const qfoajS JObEkl = { 16w29421, 128w95547459705524901484537366694330232698, 16w61546, ((bit<136>)136w13991247557688475180604247495188733374369)[130:3] - 128w12136528696822575801290694515714906259 };
        MltzXj[41:26] = h.REKU.Wikt;
        bit<128> VPhHmy = 128w215738254764408734078163211214074519634;
        h.Myng[5].ZmTx = 64w14233556188750276868;
        switch (aNlutI.apply().action_run) {
            NFyGP: {
                gmIGIlO(4w5);
                const bit<8> XraSXe = (false ? 8w216 : 8w211 |+| (8w160 - (8w48 - 8w78)));
                gmIGIlO(-4w1 << 4w10 | (4w1 | 4w6));
                const wTAbcY XKtyLA = { 32w3788658784, (false ? 217w95650687662425563809230775606976938541095215231704576245793107940[182:55] : 128w202519525649750976335750282832271457749) };
                h.REKU.hqpM = h.REKU.Wikt;
                WuyHJs[126:63] = h.Myng[4].ZmTx;
            }
        }

        h.DdBQ.AFcj = 16w42793;
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

