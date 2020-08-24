#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header bTJAgU {
    bit<8> SMTM;
}

struct DgmJiu {
    bit<4>   NKXI;
    bit<8>   dcuV;
    bit<64>  meUv;
    bit<128> HaIc;
    bit<32>  zLSu;
}

struct ZfXnaC {
    bit<4>  duDS;
    bit<16> jXdM;
    bit<8>  wffb;
    bit<8>  SYts;
    bit<32> LpZF;
}

header lzNWSW {
    bit<32> waVr;
    bit<64> AgWs;
    bit<4>  Lwhw;
    bit<4>  padding;
}

header qtXVDA {
    bit<64> Pmyg;
    bit<8>  AgUR;
    bit<8>  iMjO;
    bit<16> nhVC;
}

header AEapgd {
    bit<64> IjZK;
    bit<8>  mmdd;
    bit<64> PwfC;
    bit<4>  VXDX;
    bit<4>  padding;
}

header gOyQnY {
    bit<32> qRTi;
    bit<32> JEMK;
    bit<8>  jnKd;
}

struct Headers {
    ethernet_t eth_hdr;
    AEapgd     caqu;
    ethernet_t ROtF;
    gOyQnY     oFiN;
    ethernet_t TulV;
}

struct ingress_metadata_t {
}

struct egress_metadata_t {
}

control RJFCuAv(bit<8> kleb) {
    bit<8> djZaoH = 8w84;
    ingress_metadata_t gjjSmc = {  };
    bit<16> MdqtHn = (false ? ((bit<150>)djZaoH)[70:4][32:17] : (bit<16>)djZaoH);
    action Yfosl(in bit<16> fGll, bit<32> riPD) {
        if (true || !true) {
            return;
        } else {
            return;
        }
        djZaoH = kleb & 8w39;
        djZaoH = 8w188;
        MdqtHn = 16w1108 * 16w29733;
        bit<16> sINfoT = 16w46363;
        MdqtHn = sINfoT;
    }
    action UOkdY() {
        Yfosl((!false ? MdqtHn : 16w22478), 32w2276635332 / 32w3474855445);
        djZaoH = 8w73;
        MdqtHn = MdqtHn;
        djZaoH = 8w174;
        const bit<64> ozovEE = 64w10618062236702825774;
        djZaoH = 8w92;
        djZaoH = (true ? ~(bit<8>)-1317940061 : djZaoH);
        djZaoH = -8w106;
        MdqtHn = 16w7202;
        MdqtHn = 16w65309;
    }
    action fmWAF() {
        MdqtHn = -2007449689 - 16w31350;
        MdqtHn = MdqtHn | 16w45105;
        djZaoH = djZaoH;
        MdqtHn = MdqtHn;
        MdqtHn = 16w51897;
        bit<128> dnWyBX = 128w260640967192441504019433710498820243788;
        MdqtHn = 16w51516 % 16w39104;
        dnWyBX[99:84] = ((true || false || (!(111w363275948946082684061459721487981 != 111w1488498434074796631198509746917374) || true) && !!true ? (bit<141>)141w2036116565289508182963329483343693221033400 : 141w2093201624858549857539021850395564208141247)[79:28] - 52w418000677881936)[33:18];
        dnWyBX = 128w214449485650587817601385458040856820296 |+| dnWyBX & 128w10234830325870542988224303661835939360 % 128w109800554379109919353987201508737141708;
        bool OsjVvH = !(false && true);
    }
    table NPiitf {
        key = {
        }
        actions = {
            UOkdY();
        }
    }
    table ptUAeS {
        key = {
            kleb                                                   : exact @name("pfsQSH") ;
            MdqtHn                                                 : exact @name("RAGipb") ;
            ~(!!NPiitf.apply().hit ? 8w148 |+| 8w162 : 8w42) & 8w62: exact @name("TBiZUs") ;
        }
        actions = {
            fmWAF();
        }
    }
    apply {
        MdqtHn = 92w3362204560061776310099864882[29:14];
        djZaoH = djZaoH;
        bool YQtStz = !!((bit<39>)MdqtHn - 39w485890280676 == 39w121185576067 << (bit<8>)39w11484913686) && false || true;
        UOkdY();
        djZaoH = djZaoH;
        djZaoH = kleb;
    }
}

bit<8> OwKldDo(in bit<128> PnUC, inout bit<128> UQhP, bit<4> XBTx) {
    UQhP = 128w291936303855171467443445212836498554834;
    {
        UQhP = UQhP;
        UQhP = (128w272666190840917698516733282935338012975 |-| 128w107232582052570606861169724791806167659 | 122w303856679676073154757934407172689860 ++ (bit<6>)XBTx) |-| 128w89425748686948352933786886731727942150;
        UQhP = 128w63832667469345795218693480152453790415;
        UQhP = 128w220930568532289655051969063029375617724;
        UQhP = 128w157014075305064768573399410832903052725;
        return 8w120;
    }
    const bit<64> ZQgJHE = 64w16722053099258933377;
    UQhP = 128w117149447960829245148478837352664520484 / 128w128038471758649486912610738462350667002;
    UQhP = UQhP;
    UQhP = 128w196210206404114919682189102325832317743;
    UQhP = 128w276519860622238653246833883554115133824;
    bit<16> MjdMmA = (bit<16>)UQhP;
    UQhP = 128w23708472624182960948611859608168106966;
    return 8w255;
}
action yDxoa() {
    {
        const bit<64> LXUIGf = ~64w7848142711644635444;
        const bit<4> outCfq = 4w5;
        {
            bit<128> uVDNXs = 128w133317154829697947549750266686195801874 & ((bit<128>)LXUIGf ^ 134w5458228813879066826996841305432375455434[132:5]);
            OwKldDo(-128w187800091977968246103270006056655968406, uVDNXs, 4w4 |+| 4w3);
        }
        bit<8> BXxnTJ = (true ? (bit<8>)50780027 : 8w30);
        BXxnTJ = 8w105;
        BXxnTJ = BXxnTJ;
        BXxnTJ = ~8w171 & BXxnTJ;
        return;
    }
    AEapgd[9] dmgwKo;
    const bit<8> LkPqDX = 8w47;
    dmgwKo[6].PwfC[56:53] = 4w4;
    dmgwKo[8].padding = 4w12;
    const bool wPxhso = 113w3682792562087820523349279154037715 == 113w3686304336370300229520041665734062 / 113w4019844529550225845819628781437860 * 113w1671223341971882929576846025524131 | -354770916 || 11w770 != 11w1245;
    bit<8> gWbGzJ = ((bit<59>)(bit<59>)dmgwKo[8].PwfC)[31:24] ^ 598099561 + -890082633;
    dmgwKo[8].mmdd = LkPqDX;
    {
        bit<128> AnEQsh = 128w216700581517883953140552256862343685538;
        OwKldDo(128w334366161347997272235874571058006992134, AnEQsh, ~((bit<4>)4w1 >> 4w0));
    }
}
bit<32> fuRpubi(bit<16> ihfW) {
    bit<4> nlsyQV = (bit<4>)(4w5 - ~~4w6);
    nlsyQV = nlsyQV;
    nlsyQV = (false ? (bit<4>)-968807438 : nlsyQV ^ 4w14);
    {
        bit<128> zQNwEh = 1943248970 - 468633367;
        OwKldDo(128w309190178771446587503873487073108043315, zQNwEh, ((bit<90>)90w427694958576388524866109666)[27:24]);
    }
    return (bit<32>)nlsyQV;
}
parser SwitchIngressParser(packet_in pkt, out Headers hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        pkt.extract(ig_intr_md);
        pkt.advance(PORT_METADATA_SIZE);
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.caqu);
        pkt.extract(hdr.ROtF);
        pkt.extract(hdr.oFiN);
        pkt.extract(hdr.TulV);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    bit<64> HHPJwr = 64w7827921333377649038;
    bit<8> pYMGIu = 8w241;
    bit<64> YhbezY = 64w193329402213500238;
    bit<128> YQEhjo = 128w215533273240904997802323684313400495213;
    bit<64> NktXTE = h.caqu.IjZK;
    RJFCuAv() Apcikx;
    action XQqVI(inout bit<16> NlCD, in bit<64> GcjE, bit<128> wYhD) {
        const int fKpDJr = 962787124 + 1278019654 % 1404422170;
        h.TulV.src_addr = -48w63946073823150;
        const bit<64> JFBiSz = 64w1928065686661804504;
        OwKldDo((bit<128>)-wYhD |-| (bit<128>)(bit<128>)OwKldDo(YQEhjo & (--167291324 - fKpDJr | 128w70850454471347295388676727233220804070), YQEhjo, 4w12), YQEhjo, 4w10);
    }
    action twWak(bit<16> Ycwx, bit<4> AVLK, bit<4> kSQg) {
        bit<4> GFiTkY = (true ? (-15w928 != 15w34 ? 4w15 : 4w8) |-| AVLK : (bit<4>)-276529321);
        bit<64> sTfppS = ((bit<64>)(64w8680468256944897222 / 64w15937168156329471067) << (bit<8>)NktXTE) |-| h.caqu.PwfC;
        YQEhjo = 1765628004 ^ -371196115;
        h.caqu.IjZK = (bit<64>)64w15605166413642521473 |+| 64w14600970598117146238;
        OwKldDo(128w222399907347487270422132545242208165114, YQEhjo, 1419594027 / 1946952341);
        h.eth_hdr.src_addr = 48w49139497524190;
        YhbezY = (true ? (bit<64>)64w3058593088170028412 << (bit<8>)(false && 2085797520 != 37w55731722939 ? (bit<64>)64w9338847734400692737 : 64w4165625274896036612) : 64w6501350195245118814) |-| 64w2126037259118524315;
        h.caqu.padding = -(4w11 ^ (!false ? (bit<61>)1999106214 : (bit<61>)h.oFiN.qRTi)[14:11]);
        OwKldDo(2086530111 + 128w236934427007039541576604323193409097055 % 128w57481707067967441377786394859870477644, YQEhjo, (bit<4>)4w12 |+| 4w10);
        YQEhjo = 128w145369144298104413363229923880108525147;
        h.TulV.src_addr = 48w117756274805061 >> (bit<8>)(h.TulV.dst_addr | (bit<48>)OwKldDo(YQEhjo, YQEhjo, 4w11));
    }
    table CJpFkT {
        key = {
            h.ROtF.eth_type: exact @name("muOBIJ") ;
            ~-h.oFiN.jnKd  : exact @name("NyRZVY") ;
        }
        actions = {
        }
    }
    table wYYpeN {
        key = {
            (bit<128>)fuRpubi((69w574061711014412710372 % 69w74556291065510693318)[54:39] + 16w29546)                : exact @name("vzocVD") ;
            128w128234653624487572385148536037140299746 / 128w75878075174561606323374304718438395544                 : exact @name("yefPpI") ;
            ((bit<106>)fuRpubi(16w13061 % 16w42460))[60:45] ^ (bit<16>)fuRpubi(16w32277 * 16w31027) + h.TulV.eth_type: exact @name("viyGEf") ;
        }
        actions = {
            twWak();
        }
    }
    table ZoCkFt {
        key = {
            (true ? 4w10 : 4w13) + ((bit<102>)HHPJwr | (bit<102>)YQEhjo)[24:21]: exact @name("uXncAd") ;
        }
        actions = {
            XQqVI(h.ROtF.eth_type, (bit<64>)(bit<64>)(64w3123420118428084851 |+| 64w16027337667276388036 |-| 64w8089435688601550937));
            twWak();
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        YQEhjo = YQEhjo;
        h.eth_hdr.dst_addr[45:30] = (52w703176917836130 != (bit<52>)OwKldDo((128w77274834900423669015049547305305231115 ^ YQEhjo) |+| (CJpFkT.apply().hit ? (bit<128>)-98822378 : 128w208068824444342532977322962496175346229), YQEhjo, 4w10 + 263644574 / 1072974306) ? (bit<16>)(bit<16>)OwKldDo(128w117062472601871985451067939323999952226, YQEhjo, 4w14) : ~-(bit<16>)fuRpubi(((bit<61>)-688270069)[40:25]));
        YQEhjo = ((bit<218>)856554818)[134:7];
        h.ROtF.eth_type = -(8w211 - 8w252) ++ -8w228;
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

