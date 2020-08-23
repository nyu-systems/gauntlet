#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>


header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct rzfPRC {
    ethernet_t KJoK;
    ethernet_t YPYg;
    ethernet_t Wqlc;
}

struct qjgovu {
    ethernet_t ReuQ;
    ethernet_t minc;
}

header ZseHRV {
    bit<8> xZeP;
}

struct DctkQo {
    ethernet_t vGkq;
    ethernet_t xEIN;
    ZseHRV     dmZj;
    ethernet_t SFdP;
}

header jGQRJs {
    bit<64>  tkzA;
    bit<128> MyIK;
    bit<16>  XKtJ;
}

struct edijUo {
    jGQRJs     aEkM;
    jGQRJs     vhkW;
    ethernet_t sgyS;
}

struct IwEHHa {
    ZseHRV     uDyY;
    ethernet_t iUdA;
    jGQRJs     hMjh;
    jGQRJs     stGC;
}

struct OAgCkd {
    ZseHRV     TMIn;
    ZseHRV     nlGc;
    ethernet_t bFYy;
    ethernet_t MJvw;
    ZseHRV     pefD;
}

struct Headers {
    ethernet_t eth_hdr;
    jGQRJs     LuTo;
    ZseHRV     OANB;
}

struct ingress_metadata_t {
}

struct egress_metadata_t {
}

action PpdmQ(inout bit<32> KqZX, inout bit<64> dlZk) {
    {
        dlZk = 64w1549860199;
        KqZX = KqZX |+| 32w280517983;
        {
            {
                return;
                KqZX = ((bit<47>)dlZk)[42:11];
                bit<128> TcVqEq = (168w647071918[153:26] << (bit<8>)-128w1945578304) |-| (bit<128>)dlZk;
                {
                    KqZX = (KqZX & KqZX) * (64w1736035949 | 64w1532158386 == 64w1511033246 ? KqZX : 32w258602111);
                    TcVqEq = 128w261717261 * 128w1898057550;
                    TcVqEq = (true ? 128w968770193 - TcVqEq : (bit<128>)1883910416) - 154w1866309609[139:12];
                    dlZk = -82598204;
                }
                TcVqEq = 128w600169419 |-| 128w274274905;
                TcVqEq = TcVqEq;
                dlZk = 64w1561621281 | ((!!(1784004202 != 68w925170880) || !((bit<73>)dlZk != 73w270926219) ? (bit<64>)dlZk : 64w1280048227 + 64w252176864) | 64w237563021);
                KqZX = KqZX;
                KqZX = 32w66488042;
            }
            KqZX = KqZX;
            if (false) {
                KqZX = 1281617301;
            } else {
                dlZk = dlZk;
            }
            KqZX = (bit<32>)((true ? 128w1793831150[70:39] : 32w1135203487) + 32w364927798);
        }
        KqZX = (false ? KqZX : (bit<32>)1797242391) |-| 32w888030882;
        dlZk = 64w2108977940;
        KqZX = KqZX;
        KqZX = 32w1930853362;
    }
    KqZX = 32w2121367412;
    KqZX = 32w438672719 << (bit<8>)32w1235754302;
    dlZk = 64w552427497;
}
action JBHLs(inout bit<128> vZPe) {
    {
        bit<32> BpqqXo = 32w1814930874;
        bit<64> YCOQsD = 64w1796611945;
        PpdmQ(BpqqXo, YCOQsD);
    }
    vZPe = 19639840;
    if (!!!true) {
        vZPe = vZPe;
    } else {
        vZPe = (bit<128>)128w643235997;
    }
    vZPe = 345802468;
}
parser SwitchIngressParser(packet_in pkt, out Headers hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        pkt.extract(ig_intr_md);
        pkt.advance(PORT_METADATA_SIZE);
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.LuTo);
        pkt.extract(hdr.OANB);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    jGQRJs AQppiR = h.LuTo;
    bit<16> fFFLTi = h.LuTo.XKtJ;
    bool XQFRYe = true;
    bool STuEtM = !!XQFRYe;
    action Bxrvn(inout bit<8> CsIN, out bit<8> VqkN, in bit<32> ZwfT) {
        JBHLs(AQppiR.MyIK);
        if (90w749520734 ^ 90w489170141 != 203w1505202253[122:33] | 90w1930466787) {
            h.LuTo.tkzA = 64w634539412 |-| (64w1192887437 | AQppiR.tkzA);
        } else {
            h.eth_hdr.dst_addr = 48w1202934093 % 48w2080874025;
        }
        {
            bit<32> LgcZhA = 32w1906549792;
            PpdmQ(LgcZhA, h.LuTo.tkzA);
        }
        JBHLs(AQppiR.MyIK);
        VqkN = 8w124 + (h.OANB.xZeP - CsIN);
        h.OANB.xZeP = 8w242;
        h.LuTo.tkzA = 21w1483283 ++ 43w338682707;
        bool jASyxD = !STuEtM;
    }
    table cQoyjm {
        key = {
            ((bit<219>)AQppiR.MyIK)[194:67]: exact @name("cJtcpW") ;
            h.OANB.xZeP                    : exact @name("HOxxWr") ;
            64w1097261752                  : exact @name("ZDVIDQ") ;
        }
        actions = {
            JBHLs(h.LuTo.MyIK);
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        h.eth_hdr.src_addr = (!XQFRYe ? 48w1022824448 : (bit<48>)1205102184);
        h.eth_hdr.src_addr = 48w2006561951;
        h.OANB.xZeP = 8w0;
        JBHLs(AQppiR.MyIK);
        h.LuTo.XKtJ = 16w42814;
        cQoyjm.apply();
        h.eth_hdr.dst_addr = 48w1300524750;
        h.LuTo.tkzA = 190341637;
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

