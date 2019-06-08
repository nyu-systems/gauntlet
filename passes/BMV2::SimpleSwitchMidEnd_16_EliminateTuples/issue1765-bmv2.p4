--- dumps/pruned/issue1765-bmv2-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-06-08 18:32:10.950341600 +0200
+++ dumps/pruned/issue1765-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-06-08 18:32:10.952459600 +0200
@@ -116,14 +116,28 @@ control cEgress(inout headers hdr, inout
     apply {
     }
 }
+struct tuple_0 {
+    bit<4>      field;
+    bit<4>      field_0;
+    bit<8>      field_1;
+    bit<16>     field_2;
+    bit<16>     field_3;
+    bit<3>      field_4;
+    bit<13>     field_5;
+    bit<8>      field_6;
+    bit<8>      field_7;
+    bit<32>     field_8;
+    bit<32>     field_9;
+    varbit<320> field_10;
+}
 control vc(inout headers hdr, inout metadata meta) {
     apply {
-        verify_checksum<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>, varbit<320>>, bit<16>>(true, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.options }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
+        verify_checksum<tuple_0, bit<16>>(true, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.options }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
     }
 }
 control uc(inout headers hdr, inout metadata meta) {
     apply {
-        update_checksum<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>, varbit<320>>, bit<16>>(meta.b, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, meta.mystruct1.a ++ meta.mystruct1.b, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.options }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
+        update_checksum<tuple_0, bit<16>>(meta.b, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, meta.mystruct1.a ++ meta.mystruct1.b, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.options }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
     }
 }
 control DeparserI(packet_out packet, in headers hdr) {
