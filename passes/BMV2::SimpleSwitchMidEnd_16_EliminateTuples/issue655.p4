--- dumps/p4_16_samples/issue655.p4/pruned/issue655-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:31:00.733097500 +0200
+++ dumps/p4_16_samples/issue655.p4/pruned/issue655-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:31:00.737012600 +0200
@@ -29,14 +29,17 @@ control cEgress(inout Parsed_packet hdr,
     apply {
     }
 }
+struct tuple_0 {
+    bit<16> field;
+}
 control vc(inout Parsed_packet hdr, inout Metadata meta) {
     apply {
-        verify_checksum<tuple<bit<16>>, bit<16>>(true, { hdr.h.d }, hdr.h.c, HashAlgorithm.csum16);
+        verify_checksum<tuple_0, bit<16>>(true, { hdr.h.d }, hdr.h.c, HashAlgorithm.csum16);
     }
 }
 control uc(inout Parsed_packet hdr, inout Metadata meta) {
     apply {
-        update_checksum<tuple<bit<16>>, bit<16>>(true, { hdr.h.d }, hdr.h.c, HashAlgorithm.csum16);
+        update_checksum<tuple_0, bit<16>>(true, { hdr.h.d }, hdr.h.c, HashAlgorithm.csum16);
     }
 }
 V1Switch<Parsed_packet, Metadata>(parserI(), vc(), cIngress(), cEgress(), uc(), DeparserI()) main;
