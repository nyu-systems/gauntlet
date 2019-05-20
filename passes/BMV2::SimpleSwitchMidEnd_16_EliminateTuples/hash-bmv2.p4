--- dumps/p4_16_samples/hash-bmv2.p4/pruned/hash-bmv2-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:29:54.209941100 +0200
+++ dumps/p4_16_samples/hash-bmv2.p4/pruned/hash-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:29:54.215839900 +0200
@@ -26,9 +26,12 @@ control ComputeChecksumI(inout H hdr, in
     apply {
     }
 }
+struct tuple_0 {
+    bit<32> field;
+}
 control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
     @name("IngressI.a") action a_0() {
-        hash<bit<16>, bit<16>, tuple<bit<32>>, bit<32>>(meta.hash.hash, HashAlgorithm.crc16, 16w0, { meta.ipv4.lkp_ipv4_sa }, 32w65536);
+        hash<bit<16>, bit<16>, tuple_0, bit<32>>(meta.hash.hash, HashAlgorithm.crc16, 16w0, { meta.ipv4.lkp_ipv4_sa }, 32w65536);
     }
     apply {
         a_0();
