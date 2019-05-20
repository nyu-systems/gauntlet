--- dumps/p4_16_samples/constant-in-calculation-bmv2.p4/pruned/constant-in-calculation-bmv2-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:29:25.400978800 +0200
+++ dumps/p4_16_samples/constant-in-calculation-bmv2.p4/pruned/constant-in-calculation-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:29:25.403726700 +0200
@@ -31,9 +31,12 @@ control deparser(packet_out b, in Header
         b.emit<hdr>(h.h);
     }
 }
+struct tuple_0 {
+    bit<16> field;
+}
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
     apply {
-        hash<bit<16>, bit<10>, tuple<bit<16>>, bit<10>>(h.h.a, HashAlgorithm.crc16, 10w0, { 16w1 }, 10w4);
+        hash<bit<16>, bit<10>, tuple_0, bit<10>>(h.h.a, HashAlgorithm.crc16, 10w0, { 16w1 }, 10w4);
         sm.egress_spec = 9w0;
     }
 }
