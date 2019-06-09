#include <core.p4>
#include <v1model.p4>
typedef bit<48> EthernetAddress;
header ethernet_t {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}
struct fwd_meta_t {
    bit<16> tmp;
    bit<32> x1;
    bit<16> x2;
    bit<32> x3;
    bit<32> x4;
    bit<16> exp_etherType;
    bit<32> exp_x1;
    bit<16> exp_x2;
    bit<32> exp_x3;
    bit<32> exp_x4;
}
struct metadata {
    bit<16> _fwd_meta_tmp0;
    bit<32> _fwd_meta_x11;
    bit<16> _fwd_meta_x22;
    bit<32> _fwd_meta_x33;
    bit<32> _fwd_meta_x44;
    bit<16> _fwd_meta_exp_etherType5;
    bit<32> _fwd_meta_exp_x16;
    bit<16> _fwd_meta_exp_x27;
    bit<32> _fwd_meta_exp_x38;
    bit<32> _fwd_meta_exp_x49;
}
struct headers {
    ethernet_t ethernet;
}
parser IngressParserImpl(packet_in buffer, out headers hdr, inout metadata user_meta, inout standard_metadata_t standard_metadata) {
    state start {
        buffer.extract<ethernet_t>(hdr.ethernet);
        transition accept;
    }
}
control ingress(inout headers hdr, inout metadata user_meta, inout standard_metadata_t standard_metadata) {
    @name(".NoAction") action NoAction_0() {
    }
    @name("ingress.debug_table_cksum1") table debug_table_cksum1_0 {
        key = {
            hdr.ethernet.srcAddr              : exact @name("hdr.ethernet.srcAddr") ;
            hdr.ethernet.dstAddr              : exact @name("hdr.ethernet.dstAddr") ;
            hdr.ethernet.etherType            : exact @name("hdr.ethernet.etherType") ;
            user_meta._fwd_meta_exp_etherType5: exact @name("user_meta.fwd_meta.exp_etherType") ;
            user_meta._fwd_meta_tmp0          : exact @name("user_meta.fwd_meta.tmp") ;
            user_meta._fwd_meta_exp_x16       : exact @name("user_meta.fwd_meta.exp_x1") ;
            user_meta._fwd_meta_x11           : exact @name("user_meta.fwd_meta.x1") ;
            user_meta._fwd_meta_exp_x27       : exact @name("user_meta.fwd_meta.exp_x2") ;
            user_meta._fwd_meta_x22           : exact @name("user_meta.fwd_meta.x2") ;
            user_meta._fwd_meta_exp_x38       : exact @name("user_meta.fwd_meta.exp_x3") ;
            user_meta._fwd_meta_x33           : exact @name("user_meta.fwd_meta.x3") ;
            user_meta._fwd_meta_exp_x49       : exact @name("user_meta.fwd_meta.exp_x4") ;
            user_meta._fwd_meta_x44           : exact @name("user_meta.fwd_meta.x4") ;
        }
        actions = {
            NoAction_0();
        }
        default_action = NoAction_0();
    }
    apply {
        user_meta._fwd_meta_tmp0 = ~hdr.ethernet.etherType;
        user_meta._fwd_meta_x11 = (bit<32>)~hdr.ethernet.etherType;
        user_meta._fwd_meta_x22 = ((bit<32>)~hdr.ethernet.etherType)[31:16] + ((bit<32>)~hdr.ethernet.etherType)[15:0];
        user_meta._fwd_meta_x33 = (bit<32>)~hdr.ethernet.etherType;
        user_meta._fwd_meta_x44 = ~(bit<32>)hdr.ethernet.etherType;
        user_meta._fwd_meta_exp_etherType5 = 16w0x800;
        user_meta._fwd_meta_exp_x16 = 32w0xf7ff;
        user_meta._fwd_meta_exp_x27 = 16w0xf7ff;
        user_meta._fwd_meta_exp_x38 = 32w0xf7ff;
        user_meta._fwd_meta_exp_x49 = 32w0xfffff7ff;
        hdr.ethernet.dstAddr = 48w0;
        if (hdr.ethernet.etherType != 16w0x800) 
            hdr.ethernet.dstAddr = hdr.ethernet.dstAddr & ~48w0xff0000000000 | (bit<48>)8w1 << 40 & 48w0xff0000000000;
        if ((bit<32>)~hdr.ethernet.etherType != 32w0xf7ff) 
            hdr.ethernet.dstAddr = hdr.ethernet.dstAddr & ~48w0xff00000000 | (bit<48>)8w1 << 32 & 48w0xff00000000;
        if (((bit<32>)~hdr.ethernet.etherType)[31:16] + ((bit<32>)~hdr.ethernet.etherType)[15:0] != 16w0xf7ff) 
            hdr.ethernet.dstAddr = hdr.ethernet.dstAddr & ~48w0xff000000 | (bit<48>)8w1 << 24 & 48w0xff000000;
        if ((bit<32>)~hdr.ethernet.etherType != 32w0xf7ff) 
            hdr.ethernet.dstAddr = hdr.ethernet.dstAddr & ~48w0xff0000 | (bit<48>)8w1 << 16 & 48w0xff0000;
        if (~(bit<32>)hdr.ethernet.etherType != 32w0xfffff7ff) 
            hdr.ethernet.dstAddr = hdr.ethernet.dstAddr & ~48w0xff00 | (bit<48>)8w1 << 8 & 48w0xff00;
        debug_table_cksum1_0.apply();
    }
}
control egress(inout headers hdr, inout metadata user_meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}
control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit<ethernet_t>(hdr.ethernet);
    }
}
control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}
control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}
V1Switch<headers, metadata>(IngressParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;
