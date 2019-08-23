#include <core.p4>
#include <v1model.p4>
header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}
header p4calc_t {
    bit<8>  p;
    bit<8>  four;
    bit<8>  ver;
    bit<8>  op;
    bit<32> operand_a;
    bit<32> operand_b;
    bit<32> res;
}
struct headers {
    ethernet_t ethernet;
    p4calc_t   p4calc;
}
struct metadata {
}
parser MyParser(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    p4calc_t tmp;
    p4calc_t tmp_1;
    p4calc_t tmp_2;
    state start {
        packet.extract<ethernet_t>(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x1234: check_p4calc;
            default: accept;
        }
    }
    state check_p4calc {
        tmp = packet.lookahead<p4calc_t>();
        tmp_1 = packet.lookahead<p4calc_t>();
        tmp_2 = packet.lookahead<p4calc_t>();
        transition select(tmp.p, tmp_1.four, tmp_2.ver) {
            (8w0x50, 8w0x34, 8w0x1): parse_p4calc;
            default: accept;
        }
    }
    state parse_p4calc {
        packet.extract<p4calc_t>(hdr.p4calc);
        transition accept;
    }
}
control MyVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}
control MyIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    bit<48> tmp_0;
    bit<32> nbase_0;
    bit<64> ncount_0;
    bit<32> nselect_0;
    bit<32> ninput_0;
    @name("send_back") action send_back_0(bit<32> result_0) {
        hdr.p4calc.res = result_0;
        tmp_0 = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
        hdr.ethernet.srcAddr = tmp_0;
        standard_metadata.egress_spec = standard_metadata.ingress_port;
    }
    @name("operation_add") action operation_add_0() {
        send_back_0(hdr.p4calc.operand_a + hdr.p4calc.operand_b);
    }
    @name("operation_sub") action operation_sub_0() {
        send_back_0(hdr.p4calc.operand_a - hdr.p4calc.operand_b);
    }
    @name("operation_and") action operation_and_0() {
        send_back_0(hdr.p4calc.operand_a & hdr.p4calc.operand_b);
    }
    @name("operation_or") action operation_or_0() {
        send_back_0(hdr.p4calc.operand_a | hdr.p4calc.operand_b);
    }
    @name("operation_xor") action operation_xor_0() {
        send_back_0(hdr.p4calc.operand_a ^ hdr.p4calc.operand_b);
    }
    @name("operation_crc") action operation_crc_0() {
        nbase_0 = hdr.p4calc.operand_b;
        ncount_0 = 64w8589934592;
        ninput_0 = hdr.p4calc.operand_a;
        hash<bit<32>, bit<32>, tuple<bit<32>>, bit<64>>(nselect_0, HashAlgorithm.crc32, nbase_0, { ninput_0 }, ncount_0);
        send_back_0(nselect_0);
    }
    @name("operation_drop") action operation_drop_0() {
        mark_to_drop(standard_metadata);
    }
    @name("calculate") table calculate_0 {
        key = {
            hdr.p4calc.op: exact @name("hdr.p4calc.op") ;
        }
        actions = {
            operation_add_0();
            operation_sub_0();
            operation_and_0();
            operation_or_0();
            operation_xor_0();
            operation_crc_0();
            operation_drop_0();
        }
        const default_action = operation_drop_0();
        const entries = {
                        8w0x2b : operation_add_0();
                        8w0x2d : operation_sub_0();
                        8w0x26 : operation_and_0();
                        8w0x7c : operation_or_0();
                        8w0x5e : operation_xor_0();
                        8w0x3e : operation_crc_0();
        }
    }
    apply {
        if (hdr.p4calc.isValid()) {
            calculate_0.apply();
        } else {
            operation_drop_0();
        }
    }
}
control MyEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}
control MyComputeChecksum(inout headers hdr, inout metadata meta) {
    apply {
        update_checksum<tuple<bit<32>>, bit<32>>(hdr.p4calc.isValid(), { hdr.p4calc.operand_a }, hdr.p4calc.res, HashAlgorithm.crc32);
    }
}
control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit<ethernet_t>(hdr.ethernet);
        packet.emit<p4calc_t>(hdr.p4calc);
    }
}
V1Switch<headers, metadata>(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(), MyComputeChecksum(), MyDeparser()) main;
