--- dumps/p4_16_samples/basic_routing-bmv2.p4/pruned/basic_routing-bmv2-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:29:10.762056300 +0200
+++ dumps/p4_16_samples/basic_routing-bmv2.p4/pruned/basic_routing-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:29:10.768501400 +0200
@@ -182,14 +182,27 @@ control DeparserImpl(packet_out packet,
         packet.emit<ipv4_t>(hdr = hdr.ipv4);
     }
 }
+struct tuple_0 {
+    bit<4>  field;
+    bit<4>  field_0;
+    bit<8>  field_1;
+    bit<16> field_2;
+    bit<16> field_3;
+    bit<3>  field_4;
+    bit<13> field_5;
+    bit<8>  field_6;
+    bit<8>  field_7;
+    bit<32> field_8;
+    bit<32> field_9;
+}
 control verifyChecksum(inout headers hdr, inout metadata meta) {
     apply {
-        verify_checksum<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(condition = true, data = { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, checksum = hdr.ipv4.hdrChecksum, algo = HashAlgorithm.csum16);
+        verify_checksum<tuple_0, bit<16>>(condition = true, data = { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, checksum = hdr.ipv4.hdrChecksum, algo = HashAlgorithm.csum16);
     }
 }
 control computeChecksum(inout headers hdr, inout metadata meta) {
     apply {
-        update_checksum<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(condition = true, data = { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, checksum = hdr.ipv4.hdrChecksum, algo = HashAlgorithm.csum16);
+        update_checksum<tuple_0, bit<16>>(condition = true, data = { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, checksum = hdr.ipv4.hdrChecksum, algo = HashAlgorithm.csum16);
     }
 }
 V1Switch<headers, metadata>(p = ParserImpl(), vr = verifyChecksum(), ig = ingress(), eg = egress(), ck = computeChecksum(), dep = DeparserImpl()) main;
