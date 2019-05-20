--- dumps/p4_16_samples/issue430-bmv2.p4/pruned/issue430-bmv2-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:30:49.002462100 +0200
+++ dumps/p4_16_samples/issue430-bmv2.p4/pruned/issue430-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:30:49.005063700 +0200
@@ -17,10 +17,13 @@ control MyVerifyChecksum(inout my_packet
     apply {
     }
 }
+struct tuple_0 {
+    bit<32> field;
+}
 control MyIngress(inout my_packet p, inout my_metadata m, inout standard_metadata_t s) {
     bit<32> x;
     apply {
-        hash<bit<32>, bit<32>, tuple<bit<32>>, bit<32>>(x, HashAlgorithm.crc32, 32w0, { p.h.f ^ 32w0xffff }, 32w65536);
+        hash<bit<32>, bit<32>, tuple_0, bit<32>>(x, HashAlgorithm.crc32, 32w0, { p.h.f ^ 32w0xffff }, 32w65536);
     }
 }
 control MyEgress(inout my_packet p, inout my_metadata m, inout standard_metadata_t s) {
