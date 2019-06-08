--- dumps/pruned/psa-example-parser-checksum-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:34:10.518677600 +0200
+++ dumps/pruned/psa-example-parser-checksum-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:34:10.562844200 +0200
@@ -83,8 +83,11 @@ parser IngressParserImpl(packet_in buffe
     }
 }
 control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
-    @name(".ingress_drop") action ingress_drop(inout psa_ingress_output_metadata_t meta_1) {
+    psa_ingress_output_metadata_t meta_1;
+    @name(".ingress_drop") action ingress_drop() {
+        meta_1 = ostd;
         meta_1.drop = true;
+        ostd = meta_1;
     }
     @name("ingress.parser_error_counts") DirectCounter<PacketCounter_t>(PSA_CounterType_t.PACKETS) parser_error_counts;
     @name("ingress.set_error_idx") action set_error_idx_0(ErrorIndex_t idx) {
@@ -113,7 +116,7 @@ control ingress(inout headers hdr, inout
     apply {
         if (istd.parser_error != error.NoError) {
             parser_error_count_and_convert.apply();
-            ingress_drop(ostd);
+            ingress_drop();
             exit;
         }
     }
